/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.KrullDimension
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.Sites.TorsionSheaf
import WeilConjectures.AlgebraicGeometry.ProEtale.Classical.ProEtaleClassicalBounds
import WeilConjectures.AlgebraicGeometry.Abelian.AbelianEtaleProEtaleCohomologyComparison
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.CategoryTheory.Sites.SheafCohomologyModules
import WeilConjectures.CategoryTheory.RightDerivedExactComposite
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Forget
import WeilConjectures.CategoryTheory.Sites.SheafCohomologyRightDerived

/-!
# The uniform affine étale bound for ordinary finite-coefficient module sheaves

Source: blueprint, `sk-prop-pe-unbounded-classical-unit.proof.md`, Fixed-degree truncation;
Stacks Project, Tags 099W and 03FD (blueprint: lem-sfb-etale-module-affine-bound).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Higher cohomology of any constant-ring module sheaf on an affine étale object vanishes
above the uniform bound `2 * d_X + 1`. The module inverse image is expressed using the
canonical constant-scalar restriction and extension equivalence around `Etale.upperStar`.
The conclusion evaluates an arbitrary injective resolution of that module inverse image
at the terminal étale object of W and takes its cohomology. Integer degrees above the
positive bound are nonnegative, so `q.toNat` retains precisely the stated degree.

Source: blueprint, `sk-prop-pe-unbounded-classical-unit.proof.md`, Fixed-degree truncation;
Stacks Project, Tags 099W and 03FD (blueprint: lem-sfb-etale-module-affine-bound).

Proof (the six steps of the node):
1. Put N = ℓ^a. The scalar N * 1 is zero, so N kills every section of the underlying
abelian sheaf of G. It is torsion, with no finiteness requirement on its sections.
2. Mathlib supplies that the étale map w is weakly étale. The one-object constant
presentation of the affine scheme W is a pro-étale affine presentation over X in the
sense of `definition-ind-etale-pro-etale-weakly`; its only transition is the affine identity.
3. Apply `lemma-uniform-bounds-pro-etale-affines` (1) with Y = X and g = identity. It gives
vanishing on W's pro-étale site above exactly the displayed bound, including empty X.
4. `comparisonUpperStarCompUpperStarIso` identifies the two pulled-back coefficients.
`lem-cbc-abelian-etale-proetale-cohomology-comparison` (Stacks 099W) transfers the
vanishing to abelian cohomology on W's étale site. The positive bound ensures q ≥ 0.
5. `upperStarForget₂Comparison` identifies the underlying abelian sheaf of module
inverse image with the abelian inverse image, using the constant-ring module equivalence.
6. The constant-ring equivalence supplies enough injectives and preserves injectivity.
`subsingleton_H_forget₂_of_injective` makes their underlying abelian sheaves acyclic.
The exact-composite comparison `exists_rightDerived_exact_comp_iso` (Stacks 03FD and
015M) computes abelian sections on the chosen module injective resolution. Exact scalar
forgetting commutes with homology and reflects zero objects, giving the claimed vanishing.
No flatness, constructibility, finite generation, or injectivity after forgetting scalars
is needed. -/
theorem etaleModule_affine_cohomology_isZero
    {k : Type u} [Field k] (hk : Finite k ∨ IsAlgClosed k)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓk : IsUnit (ℓ : k))
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (a : ℕ) (ha : 1 ≤ a) (hA : (ℓ : A) ^ a = 0)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    (W : X.Etale) [IsAffine W.left]
    (G : ringedSiteModules.{u + 1} (Scheme.etaleConstantModuleRing X A))
    (q : ℤ) (hq : (2 * ((topologicalKrullDim X).unbotD 0).toNat + 1 : ℕ) < q)
    (I : InjectiveResolution
      ((Scheme.etaleConstantModuleFunctor W.left A).obj
        ((Etale.upperStar (ModuleCat.{u + 1} A) W.hom).obj
          ((Scheme.etaleConstantModuleRestrictionFunctor X A).obj G)))) :
    IsZero ((((SheafOfModules.evaluation
      (Scheme.etaleConstantModuleRing W.left A)
      (op (Scheme.Etale.mk (𝟙 W.left)))).mapHomologicalComplex (.up ℕ)).obj
        I.cocomplex).homology q.toNat) := by
  have _ := hℓk
  have _ := ha
  let J := (Scheme.etaleConstantModuleRestrictionFunctor X A).obj G
  let F := (sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).obj J
  have hF : F.IsTorsion := by
    apply Scheme.isTorsion_of_nsmul_id_eq_zero (pow_pos hℓ.pos a)
    ext U s
    have hs (t : J.obj.obj U) : (ℓ ^ a) • t = 0 := by
      rw [← Nat.cast_smul_eq_nsmul A, Nat.cast_pow, hA, zero_smul]
    exact hs s
  have hqNat : 2 * ((topologicalKrullDim X).unbotD 0).toNat + 1 < q.toNat := by
    omega
  have hV : Subsingleton
      (Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1} W.hom).obj F) q.toNat) := by
    have : IsAffine ((𝟭 Scheme).obj W.left) := ‹IsAffine W.left›
    let U : X.ProEt := Scheme.ProEt.mk W.hom
    have hB := (ProEtale.hasClassicalUniformBounds hk (X ↘ Spec (.of k))
      (X ↘ Spec (.of k)) (𝟙 X) F hF).1.1 U (proAffineEtale.of_isAffine W.hom) q.toNat
        (by exact_mod_cast hqNat)
    let Fw := (Etale.upperStar AddCommGrpCat.{u + 1} W.hom).obj F
    let V := (ProEtale.comparisonUpperStar AddCommGrpCat.{u + 1} W.left).obj Fw
    let e := (ProEtale.comparisonUpperStarCompUpperStarIso
      AddCommGrpCat.{u + 1} W.hom).app F
    let Γ := Sheaf.Γ (Scheme.ProEt.topology W.left) AddCommGrpCat.{u + 1}
    have hz : IsZero ((Γ.rightDerived q.toNat).obj V) := by
      exact hB.of_iso ((DerivedCategory.homologyFunctor _ (q.toNat : ℤ)).mapIso
        ((ProEtale.rightDerivedGlobalSections AddCommGrpCat.{u + 1} W.left).mapIso
          ((DerivedCategory.singleFunctor _ 0).mapIso e)) ≪≫
            Γ.homologyRightDerivedFunctorObjSingleFunctorIso V q.toNat).symm
    have : ((sheafSections (Scheme.ProEt.topology W.left) AddCommGrpCat.{u + 1}).obj
        (op (⊤_ W.left.ProEt))).Additive := { map_add := rfl }
    have hz' := hz.of_iso ((NatIso.rightDerived
      (Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology W.left) AddCommGrpCat.{u + 1}
        terminalIsTerminal) q.toNat).app V).symm
    have hV := (Sheaf.subsingleton_H_iff_isZero_rightDerived
      (Scheme.ProEt.topology W.left) terminalIsTerminal q.toNat V).2 hz'
    exact (ProEtale.comparisonCohomologyMap_bijective W.left Fw q.toNat).1.subsingleton
  let V := (Etale.upperStar (ModuleCat.{u + 1} A) W.hom).obj J
  let R := Scheme.etaleConstantModuleRing W.left A
  let M := (Scheme.etaleConstantModuleFunctor W.left A).obj V
  let H := (SheafOfModules.toSheaf R).obj M
  let e : (Etale.upperStar AddCommGrpCat.{u + 1} W.hom).obj F ≅ H :=
    asIso (Etale.upperStarForget₂Comparison A W.hom J)
  have hH : Subsingleton (Sheaf.H H q.toNat) := by
    have hz : IsZero ((Sheaf.functorH.{u + 1} W.left.smallEtaleTopology q.toNat).obj
        ((Etale.upperStar AddCommGrpCat.{u + 1} W.hom).obj F)) :=
      AddCommGrpCat.isZero_iff_subsingleton.mpr hV
    exact AddCommGrpCat.isZero_iff_subsingleton.mp
      (hz.of_iso ((Sheaf.functorH.{u + 1} W.left.smallEtaleTopology q.toNat).mapIso e).symm)
  have hR := Scheme.etaleConstantModuleFunctor_isEquivalence W.left A
  have : EnoughInjectives (SheafOfModules.{u + 1} R) :=
    (Scheme.etaleConstantModuleFunctor W.left A).asEquivalence.enoughInjectives_iff.mp
      inferInstance
  have hz := (Sheaf.subsingleton_H_iff_isZero_rightDerived W.left.smallEtaleTopology
    (MorphismProperty.Over.mkIdTerminal (@Etale) W.left)
      q.toNat H).1 hH
  let T := SheafOfModules.toSheaf R
  let Γ := Sheaf.sectionsFunctorAt.{u + 1} W.left.smallEtaleTopology
    (Scheme.Etale.mk (𝟙 W.left))
  let : PreservesFiniteColimits T := (moduleSheaves_colimits_forgetful R).2.2.1
  have hE : (Scheme.etaleConstantModuleRestrictionFunctor W.left A).IsEquivalence :=
    Functor.IsEquivalence.mk' (Scheme.etaleConstantModuleFunctor W.left A)
      (Scheme.etaleConstantModuleCounitIso W.left A).symm
      (Scheme.etaleConstantModuleUnitIso W.left A).symm
  have hT (L : SheafOfModules.{u + 1} R) (hL : Injective L) :
      Γ.rightAcyclic (T.obj L) := by
    let K := (Scheme.etaleConstantModuleRestrictionFunctor W.left A).obj L
    have : Injective K := inferInstance
    intro n
    have hzL := Sheaf.subsingleton_H_forget₂_of_injective.{u + 1, u + 1, u, u + 1} A K n
    exact (Sheaf.subsingleton_H_iff_isZero_rightDerived W.left.smallEtaleTopology
      (MorphismProperty.Over.mkIdTerminal (@Etale) W.left) (n + 1) (T.obj L)).1 hzL
  obtain ⟨c, _⟩ := Functor.exists_rightDerived_exact_comp_iso T Γ hT M q.toNat
  have hz' := (hz.of_iso c).of_iso (I.isoRightDerivedObj (T ⋙ Γ) q.toNat).symm
  let E := SheafOfModules.forget.{u + 1} R ⋙
    PresheafOfModules.evaluation R.obj (op (Scheme.Etale.mk (𝟙 W.left)))
  let V₀ := forget₂ (ModuleCat.{u + 1} (R.obj.obj (op (Scheme.Etale.mk (𝟙 W.left)))))
    AddCommGrpCat.{u + 1}
  let K := (E.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  have hf : IsZero (V₀.obj (K.homology q.toNat)) :=
    hz'.of_iso ((K.sc q.toNat).mapHomologyIso V₀).symm
  rw [IsZero.iff_id_eq_zero] at hf ⊢
  apply V₀.map_injective
  change (𝟙 (V₀.obj (K.homology q.toNat))) = 0
  exact hf

end AlgebraicGeometry
