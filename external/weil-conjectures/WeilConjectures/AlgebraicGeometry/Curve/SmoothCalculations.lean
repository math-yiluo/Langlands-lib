/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import WeilConjectures.AlgebraicGeometry.Curve
import WeilConjectures.AlgebraicGeometry.ArtinSchreierSequence
import WeilConjectures.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo
import WeilConjectures.AlgebraicGeometry.Curve.Estimate
import WeilConjectures.LinearAlgebra.SemilinearFrobenius
import WeilConjectures.AlgebraicGeometry.IsProperOrIsAffine
import WeilConjectures.AlgebraicGeometry.ZeroDimensionalEtaleCohomologyRest
import WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison
import WeilConjectures.AlgebraicGeometry.Curve.ArtinSchreierProperDegreeZero
import WeilConjectures.AlgebraicGeometry.Curve.ProperConstantBaseChangeZero
import WeilConjectures.AlgebraicGeometry.Curve.ProperConstantBaseChangeOne
import WeilConjectures.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher
import WeilConjectures.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.AlgebraicGeometry.PrimeInjectiveCohomologyComparison
import WeilConjectures.AlgebraicGeometry.AlgClosedExtensionModuleSections
import WeilConjectures.AlgebraicGeometry.AlgClosedExtensionInjectiveAcyclic
import WeilConjectures.AlgebraicGeometry.CohomologyRestrictionSquareTransport
import WeilConjectures.AlgebraicGeometry.Curve.ClopenConstantAssertions
import WeilConjectures.AlgebraicGeometry.Curve.PrimeAnnihilatedPrimaryCases
import WeilConjectures.AlgebraicGeometry.Curve.PrimeTorsionNonunitCohomology
import Mathlib.Algebra.Field.ULift

/-!
# The curve assertions for constant coefficients on smooth curves

Let `k` be an algebraically closed field, `f : C ⟶ Spec k` a smooth separated connected curve
(`[IsCurve f] [Smooth f] [ConnectedSpace C]`) and `n` a prime. The constant sheaf `𝐅_n` is
read over an arbitrary coefficient ring `Λ` as the constant sheaf `Λ/nΛ`
(`AlgebraicGeometry.Etale.constantModSheaf Λ C n`), and `Hᵠ(C, 𝐅_n)` is the cohomology of its
underlying abelian sheaf, as in the eight curve assertions
`AlgebraicGeometry.IsCurve.Assertions`. This file states, for `F = 𝐅_n`, each assertion
`C₁, …, C₈` in the form of the corresponding field of `AlgebraicGeometry.IsCurve.Assertions`,
under the hypotheses of the smooth-curve calculations:

* `C₁`, `C₈` for every prime `n`; `C₂` for affine `C`; `C₅`, `C₇` for proper `C`;
* `C₄`, `C₆` for `n ≠ char k`;
* `C₃` for `n = char k = p > 0`.

## Main statements

- `AlgebraicGeometry.IsCurve.subsingleton_sheafH_constantModSheaf_of_two_lt`: `C₁`.
- `AlgebraicGeometry.IsCurve.subsingleton_sheafH_constantModSheaf_of_one_lt_of_isAffine`: `C₂`.
- `AlgebraicGeometry.IsCurve.subsingleton_sheafH_constantModSheaf_of_one_lt_of_charP`: `C₃`.
- `AlgebraicGeometry.IsCurve.finite_sheafH_constantModSheaf_of_ne_zero`: `C₄`.
- `AlgebraicGeometry.IsCurve.finite_sheafH_constantModSheaf_of_isProper`: `C₅`.
- `AlgebraicGeometry.IsCurve.bijective_cohomologyMap_constantModSheaf_of_ne_zero`: `C₆`.
- `AlgebraicGeometry.IsCurve.bijective_cohomologyMap_constantModSheaf_of_isProper`: `C₇`.
- `AlgebraicGeometry.IsCurve.surjective_cohomologyMap_constantModSheaf_two`: `C₈`.
- `AlgebraicGeometry.IsCurve.constantModSheaf_curveCalculations`: the smooth-curve
  calculations, the conjunction of the above.
- `AlgebraicGeometry.IsCurve.assertions_constantModSheaf_of_ne_zero`: all eight assertions
  for `𝐅_ℓ`, `ℓ ≠ char k`, on a smooth curve (not necessarily connected).
- `AlgebraicGeometry.IsCurve.assertions_constantModSheaf_of_charP`: all eight assertions
  for `𝐅_p`, `p = char k`, on a smooth curve (not necessarily connected).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

/-! ### Auxiliary lemmas -/

/-- The constant sheaf `Λ/nΛ` is killed by `n`: `n • 𝟙 = 0` on
`AlgebraicGeometry.Etale.constantModSheaf Λ X n`. -/
lemma Etale.nsmul_id_constantModSheaf (X : Scheme.{u}) (n : ℕ) :
    n • 𝟙 (Etale.constantModSheaf Λ X n) = 0 := by
  rw [Etale.constantModSheaf, ← (constantSheaf _ _).map_id, ← Functor.map_nsmul,
    ← (constantSheaf _ _).map_zero]
  congr 1
  ext
  simpa using (Ideal.Quotient.eq_zero_iff_mem).2 (Ideal.mem_span_singleton_self (n : Λ))

/-- For `n > 0`, the underlying abelian sheaf of the constant sheaf `Λ/nΛ` is torsion
(`CategoryTheory.Sheaf.IsTorsion`): every section is killed by `n`. -/
lemma Etale.isTorsion_constantModSheaf (X : Scheme.{u}) {n : ℕ} (hn : 0 < n) :
    ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
      (Etale.constantModSheaf Λ X n)).IsTorsion := by
  refine Sheaf.IsTorsion.of_forall_isAddTorsion fun U x ↦ ?_
  have h := congr_arg
    (fun φ => ((sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map φ).app U)
    (Etale.nsmul_id_constantModSheaf Λ X n)
  simp only [Functor.map_nsmul, NatTrans.app_nsmul, Functor.map_zero, NatTrans.app_zero] at h
  have hx := congr_arg (fun φ => φ.hom x) h
  simp only [ModuleCat.hom_nsmul, ModuleCat.hom_zero] at hx
  exact isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨n, hn, hx⟩

open CategoryTheory.Limits in
private theorem constantModSheaf_finite_biproduct (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    [Finite (Λ ⧸ (Ideal.span {(p : Λ)} : Ideal Λ))] :
    ∃ n : ℕ, Nonempty
      (((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        (Etale.constantModSheaf Λ X p)) ≅ ⨁ fun _ : Fin n ↦ X.constantZMod p) := by
  classical
  let M := Λ ⧸ (Ideal.span {(p : Λ)} : Ideal Λ)
  have hp : ∀ x : M, p • x = 0 := by
    intro x
    have hp0 : (p : M) = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem).2 (Ideal.mem_span_singleton_self (p : Λ))
    rw [nsmul_eq_mul, hp0, zero_mul]
  let : Module (ZMod p) M := AddCommGroup.zmodModule hp
  let R := ULift.{u + 1} (ZMod p)
  let : Module R M := Module.compHom M ULift.ringEquiv.toRingHom
  let B := Module.Basis.ofVectorSpaceIndex R M
  let b : Module.Basis B R M := Module.Basis.ofVectorSpace R M
  have : Finite B := Finite.of_injective b b.injective
  let : Fintype B := Fintype.ofFinite B
  let n := Fintype.card B
  let a : B → ModuleCat.{u + 1} R := fun _ ↦ ModuleCat.of R R
  let T : ModuleCat.{u + 1} R ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
    forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1} ⋙
      constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}
  let eM : (∐ a) ≅ ModuleCat.of R M :=
    (colimit.isColimit (Discrete.functor a)).coconePointUniqueUpToIso
      (ModuleCat.finsuppCoconeIsColimit R R B) ≪≫ b.repr.symm.toModuleIso
  have : PreservesLimits (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
    inferInstance
  have : X.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) := by
    apply GrothendieckTopology.instPreservesSheafification
  let e : T.obj (ModuleCat.of R M) ≅
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        (Etale.constantModSheaf Λ X p)) :=
    (constantCommuteCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).symm.app (ModuleCat.of Λ M)
  exact ⟨n, ⟨e.symm ≪≫ (T.mapIso eM).symm ≪≫ PreservesCoproduct.iso T a ≪≫
    (biproduct.isoCoproduct (fun _ : B ↦ X.constantZMod p)).symm ≪≫
    biproduct.whiskerEquiv (f := fun _ : B ↦ X.constantZMod p)
      (g := fun _ : Fin n ↦ X.constantZMod p) (Fintype.equivFin B) (fun _ ↦ Iso.refl _)⟩⟩

open CategoryTheory.Limits in
private theorem finite_constantModSheaf_of_finite_constantZMod (X : Scheme.{u})
    (p : ℕ) [Fact p.Prime] [Finite (Λ ⧸ (Ideal.span {(p : Λ)} : Ideal Λ))]
    (q : ℕ) [Finite (Sheaf.H (X.constantZMod p) q)] :
    Finite (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        (Etale.constantModSheaf Λ X p)) q) := by
  obtain ⟨n, ⟨e⟩⟩ := constantModSheaf_finite_biproduct Λ X p
  let H := Sheaf.functorH.{u + 1} X.smallEtaleTopology q
  have : Finite (H.obj (X.constantZMod p)) :=
    show Finite (Sheaf.H (X.constantZMod p) q) from inferInstance
  have : Finite (Fin n → H.obj (X.constantZMod p)) := inferInstance
  let E := (H.mapIso e ≪≫ H.mapBiproduct (fun _ : Fin n ↦ X.constantZMod p) ≪≫
    AddCommGrpCat.biproductIsoPi (fun _ : Fin n ↦ H.obj (X.constantZMod p)))
      |>.addCommGroupIsoToAddEquiv
  exact Finite.of_equiv _ E.toEquiv.symm

set_option backward.isDefEq.respectTransparency false in
open CategoryTheory.Limits in
private theorem finite_ker_artinSchreier_one
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsProper f]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (G : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})
    (a : ∀ U : C.Etaleᵒᵖ, G.obj.obj U ≃+ Γ(U.unop.left, ⊤))
    (wp : G ⟶ G)
    (ha : ∀ (U V : C.Etaleᵒᵖ) (g : U ⟶ V) (x : G.obj.obj U),
      a V (G.obj.map g x) = g.unop.left.appTop (a U x))
    (hwp : ∀ (U : C.Etaleᵒᵖ) (x : G.obj.obj U),
      a U (wp.hom.app U x) = (a U x) ^ p - a U x) :
    Finite (((Etale.cohomology AddCommGrpCat.{u + 1} C (1 : ℤ)).map
      ((DerivedCategory.singleFunctor
        (Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).map wp)).hom.ker) := by
  classical
  let T : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
    DerivedCategory.singleFunctor
    (Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) 0 ⋙
      Etale.cohomology AddCommGrpCat.{u + 1} C (1 : ℤ)
  obtain ⟨m, hfinite, hscalar⟩ :=
    exists_finiteDimensional_etaleCohomology_one_scalar_model f G a ha
  let := m
  let := hfinite
  have : T.Additive := by
    dsimp [T, Etale.cohomology, Etale.rightDerivedGlobalSections]
    infer_instance
  let φ : G ⟶ G := wp + 𝟙 G
  have hφ (U : C.Etaleᵒᵖ) (x : G.obj.obj U) :
      a U (φ.hom.app U x) = (a U x) ^ p := by
    change a U (wp.hom.app U x + x) = _
    rw [map_add, hwp, sub_add_cancel]
  have hsemi (c : k) (x : T.obj G) : T.map φ (c • x) = c ^ p • T.map φ x := by
    obtain ⟨μ, hμ, hμmap⟩ := hscalar c
    obtain ⟨ν, hν, hνmap⟩ := hscalar (c ^ p)
    have hcomm : μ ≫ φ = φ ≫ ν := by
      apply Sheaf.hom_ext
      ext U y
      apply (a U).injective
      change a U (φ.hom.app U (μ.hom.app U y)) =
        a U (ν.hom.app U (φ.hom.app U y))
      rw [hφ, hμ, hν, hφ]
      let ρ : k →+* Γ(U.unop.left, ⊤) := U.unop.hom.appTop.hom.comp
        (f.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)
      change (a U y * ρ c) ^ p = (a U y) ^ p * ρ (c ^ p)
      rw [mul_pow, map_pow]
    rw [← hμmap, ← AddCommGrpCat.comp_apply, ← T.map_comp, hcomm, T.map_comp,
      AddCommGrpCat.comp_apply, hνmap]
  let F : T.obj G →ₛₗ[frobenius k p] T.obj G :=
    { toFun := T.map φ
      map_add' := (T.map φ).hom.map_add
      map_smul' := fun c x ↦ by simpa only [frobenius_def] using hsemi c x }
  have hF (x : T.obj G) : F x - x = T.map wp x := by
    change T.map (wp + 𝟙 G) x - x = _
    rw [T.map_add, T.map_id]
    change (T.map wp x + x) - x = _
    exact add_sub_cancel_right _ _
  let j : (T.map wp).hom.ker → LinearMap.Frobenius.fixedPoints F := fun x ↦
    ⟨x, by
      rw [LinearMap.Frobenius.mem_fixedPoints]
      have hx : T.map wp x = 0 := x.property
      exact sub_eq_zero.mp ((hF x).trans hx)⟩
  change Finite (T.map wp).hom.ker
  have hinj : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : LinearMap.Frobenius.fixedPoints F ↦ (z : T.obj G)) h
  exact Finite.of_injective j hinj

open CategoryTheory.Limits in
private theorem bijective_constantModSheaf_standard_baseChange
    {k K : Type u} [Field k] [Field K] [IsAlgClosed k] [IsAlgClosed K] [Algebra k K]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [QuasiCompact f] [QuasiSeparated f]
    (r : ℕ) [Fact r.Prime] (hr : (r : k) ≠ 0)
    (F : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (hF : r • 𝟙 F = 0) (q : ℕ) :
    Function.Bijective (Etale.cohomologyMap
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q) := by
  let U := sheafCompose C.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  have hkill : r • 𝟙 (U.obj F) = 0 := by
    apply Sheaf.hom_ext
    ext V x
    have h := congr_arg
      (fun φ ↦ ((sheafToPresheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map φ).app V)
      hF
    simp only [Functor.map_nsmul, NatTrans.app_nsmul, Functor.map_zero, NatTrans.app_zero] at h
    have hx := congr_arg (fun φ ↦ φ.hom x) h
    change r • x = 0
    simpa using hx
  exact Etale.bijective_cohomologyMap_of_prime_injective_acyclic _ r
    (Etale.isIso_globalSectionsUpperStarMap_algClosed_extension f r)
    (fun J _ q hq ↦
      Etale.subsingleton_cohomology_upperStar_injective_algClosed_extension f r hr J q hq)
    (U.obj F) hkill q

namespace IsCurve

variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))

/-! ### The assertions `C₁, …, C₈` for `𝐅_n` -/

/-- **`C₁` for `𝐅_n`.** Let `C` be a smooth separated connected curve over an algebraically
closed field `k` and `n` a prime. Then `Hᵠ(C, 𝐅_n) = 0` for `q > 2`, where `𝐅_n` is the constant
sheaf `Λ/nΛ` and `Hᵠ` is the cohomology of its underlying abelian sheaf. This is the
cohomological dimension bound `AlgebraicGeometry.IsCurve.subsingleton_sheafH_of_three_le`,
the constant sheaf being killed by `n`.
(blueprint: theorem-cohomology-curves)
-/
theorem subsingleton_sheafH_constantModSheaf_of_two_lt [IsCurve f] [Smooth f] [ConnectedSpace C]
    (n : ℕ) [Fact n.Prime] (q : ℕ) (hq : 2 < q) :
    Subsingleton (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        (Etale.constantModSheaf Λ C n)) q) :=
  subsingleton_sheafH_of_three_le f _
    (Etale.isTorsion_constantModSheaf Λ C (Fact.out : n.Prime).pos) q hq

/-- **`C₂` for `𝐅_n`.** Let `C` be a smooth affine connected curve over an algebraically closed
field `k` and `n` a prime. Then `Hᵠ(C, 𝐅_n) = 0` for `q > 1`. This is the cohomological dimension
bound `AlgebraicGeometry.IsCurve.subsingleton_sheafH_of_two_le_of_isAffine`, the constant sheaf
being killed by `n`.
(blueprint: theorem-cohomology-curves)
-/
theorem subsingleton_sheafH_constantModSheaf_of_one_lt_of_isAffine [IsCurve f] [Smooth f]
    [ConnectedSpace C] [IsAffine C] (n : ℕ) [Fact n.Prime] (q : ℕ) (hq : 1 < q) :
    Subsingleton (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        (Etale.constantModSheaf Λ C n)) q) :=
  subsingleton_sheafH_of_two_le_of_isAffine f _
    (Etale.isTorsion_constantModSheaf Λ C (Fact.out : n.Prime).pos) q hq

/-- **`C₃` for `𝐅_p`.** Let `k` be algebraically closed of characteristic `p > 0` and `C` a
smooth separated connected curve over `k`. Then `Hᵠ(C, 𝐅_p) = 0` for `q > 1`: by the
Artin–Schreier sequence `0 → 𝐅_p → 𝒪_C → 𝒪_C → 0` and the surjectivity of `F - 1`, the
`p`-cohomological dimension of `C` is at most one. The `p`-primary hypothesis of the field
`C₃` of `AlgebraicGeometry.IsCurve.Assertions` holds automatically for `𝐅_p` and is omitted.
(blueprint: proposition-p-torsion-smooth-proper-curve--3)
-/
theorem subsingleton_sheafH_constantModSheaf_of_one_lt_of_charP [IsCurve f] [Smooth f]
    [ConnectedSpace C] (p : ℕ) [Fact p.Prime] [CharP k p] (q : ℕ) (hq : 1 < q) :
    Subsingleton (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        (Etale.constantModSheaf Λ C p)) q) :=
  by
    by_cases hq2 : q = 2
    · subst q
      exact subsingleton_sheafH_constantModSheaf_of_charP_two Λ f p
    · have hq' : 2 < q := by omega
      exact subsingleton_sheafH_constantModSheaf_of_two_lt Λ f p q hq'

/-- **`C₄` for `𝐅_r`.** Let `C` be a smooth separated connected curve over an algebraically
closed field `k` and `r` a prime different from `char k`. If `Λ/rΛ` is finite, then
`Hᵠ(C, 𝐅_r)` is finite for every `q`: `C` is proper or affine, and the
groups are computed by the Kummer sequence. The torsion hypothesis of the field `C₄` of
`AlgebraicGeometry.IsCurve.Assertions` is replaced by `(r : k) ≠ 0`.
(blueprint: theorem-cohomology-curves)
-/
theorem finite_sheafH_constantModSheaf_of_ne_zero [IsCurve f] [Smooth f] [ConnectedSpace C]
    (r : ℕ) [Fact r.Prime] (hr : (r : k) ≠ 0)
    [Finite (Λ ⧸ (Ideal.span {(r : Λ)} : Ideal Λ))] (q : ℕ) :
    Finite (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        (Etale.constantModSheaf Λ C r)) q) :=
  by
  classical
  have : NeZero r := ⟨(Fact.out : r.Prime).ne_zero⟩
  have hprime : Finite (Sheaf.H (C.constantZMod r) q) := by
    by_cases hq0 : q = 0
    · subst q
      obtain ⟨e⟩ := C.nonempty_addEquiv_sheafH_zero_constantZMod r
      exact Finite.of_equiv _ e.toEquiv.symm
    · by_cases hdim : topologicalKrullDim C = 1
      · have : IsConnectedCurve f :=
          { connectedSpace := inferInstance
            krullDim_eq_one := hdim }
        obtain hproper | haffine := IsConnectedCurve.isProper_or_isAffine f
        · have : IsProper f := hproper
          obtain ⟨_, ⟨e₁⟩, ⟨e₂⟩, hvan⟩ :=
            IsConnectedCurve.sheafH_constantZMod_of_isProper f r hr
          by_cases hq1 : q = 1
          · subst q
            exact Finite.of_equiv _ e₁.toEquiv.symm
          · by_cases hq2 : q = 2
            · subst q
              exact Finite.of_equiv _ e₂.toEquiv.symm
            · have := hvan q (by omega)
              infer_instance
        · have : IsAffine C := haffine
          obtain ⟨_, hunit, ⟨α, β, hα, hex, hβ⟩, hpic, hvan⟩ :=
            IsConnectedCurve.sheafH_constantZMod_of_isAffine f r hr
          by_cases hq1 : q = 1
          · subst q
            have hquot : Finite (Additive Γ(C, ⊤)ˣ ⧸ α.ker) := by
              rw [hα]
              exact hunit
            have : Finite α.range :=
              Finite.of_equiv _ (QuotientAddGroup.quotientKerEquivRange α).toEquiv
            have : Finite β.ker := by
              rw [AddMonoidHom.exact_iff.mp hex]
              infer_instance
            have : Finite β.range := by
              rw [hβ]
              exact hpic
            exact (β.finite_iff_finite_ker_range).mpr ⟨inferInstance, inferInstance⟩
          · have := hvan q (by omega)
            infer_instance
      · have hzero : topologicalKrullDim C ≤ 0 := by
          have hlt : topologicalKrullDim C < 1 :=
            lt_of_le_of_ne (IsCurve.krullDim_le_one (f := f)) hdim
          exact Order.le_of_lt_succ hlt
        have hvan := (zero_dimensional_etale_cohomology_rest k C f hzero
          (C.constantZMod r) (fun x ↦ AlgebraicClosure (C.residueField x)) C.algClosurePoint
          (fun x ↦ C.algClosurePoint_base x default)).1 q (by omega)
        obtain ⟨e⟩ := Scheme.nonempty_sheafH_extDerivedIso C q
        have hz : CategoryTheory.Limits.IsZero ((Sheaf.functorH.{u + 1} C.smallEtaleTopology q).obj
            (C.constantZMod r)) :=
          CategoryTheory.Limits.IsZero.of_iso (AddCommGrpCat.isZero_iff_subsingleton.mpr hvan)
            (e.app (C.constantZMod r))
        have : Subsingleton (Sheaf.H (C.constantZMod r) q) :=
          AddCommGrpCat.subsingleton_of_isZero hz
        infer_instance
  exact finite_constantModSheaf_of_finite_constantZMod Λ C r q

/-- **`C₅` for `𝐅_r`.** Let `C` be a smooth proper connected curve over an algebraically closed
field `k` and `r` an arbitrary prime. If `Λ/rΛ` is finite, then `Hᵠ(C, 𝐅_r)` is finite for
every `q`: for `r ≠ char k` by the curve estimates, and for
`r = char k = p` by the Artin–Schreier sequence, which identifies `H¹(C, 𝐅_p)` with the
Frobenius-fixed part of `H¹(C, 𝒪_C)` and kills the higher groups.
(blueprint: proposition-p-torsion-smooth-proper-curve--4)
-/
theorem finite_sheafH_constantModSheaf_of_isProper [IsCurve f] [Smooth f] [ConnectedSpace C]
    [IsProper f] (r : ℕ) [Fact r.Prime] [Finite (Λ ⧸ (Ideal.span {(r : Λ)} : Ideal Λ))]
    (q : ℕ) :
    Finite (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        (Etale.constantModSheaf Λ C r)) q) :=
  by
    classical
    by_cases hr : (r : k) ≠ 0
    · exact finite_sheafH_constantModSheaf_of_ne_zero Λ f r hr q
    · have : CharP k r := (CharP.charP_iff_prime_eq_zero (Fact.out : r.Prime)).mpr
        (not_ne_iff.mp hr)
      by_cases hq0 : q = 0
      · subst q
        have : NeZero r := ⟨(Fact.out : r.Prime).ne_zero⟩
        obtain ⟨e⟩ := C.nonempty_addEquiv_sheafH_zero_constantZMod r
        have : Finite (Sheaf.H (C.constantZMod r) 0) :=
          Finite.of_equiv _ e.toEquiv.symm
        exact finite_constantModSheaf_of_finite_constantZMod Λ C r 0
      · by_cases hq1 : q = 1
        · subst q
          have hprime : Finite (Sheaf.H (C.constantZMod r) 1) := by
            by_cases hdim : topologicalKrullDim C = 1
            · have : IsConnectedCurve f :=
                { connectedSpace := inferInstance
                  krullDim_eq_one := hdim }
              obtain ⟨G, _, a, wp, iota, hzero, ha, hwp, _, hS⟩ :=
                artinSchreier_shortExact f r (Fact.out : r.Prime).pos
              let R := (Sheaf.Γ C.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctor
              let T := R.mapTriangle.obj hS.singleTriangle
              have hT : T ∈ distTriang _ :=
                R.map_distinguished _ hS.singleTriangle_distinguished
              have hepi : Epi ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 0).map
                  T.mor₂) :=
                epi_etaleCohomology_artinSchreier_zero_of_isProper f r G a wp ha hwp
              have hδ := (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff
                T hT 0 1).mp hepi
              have hmono : Mono ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 1).map
                  T.mor₁) :=
                (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff T hT 0 1).mpr hδ
              let A := DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} 1
              have hker : Finite (A.map T.mor₂).hom.ker :=
                finite_ker_artinSchreier_one f r G a wp ha hwp
              have hcomp : A.map T.mor₁ ≫ A.map T.mor₂ = 0 := by
                simpa only [← Functor.map_comp, Functor.map_zero] using
                  congrArg A.map (Pretriangulated.comp_distTriang_mor_zero₁₂ T hT)
              have hfin : Finite (A.obj T.obj₁) := by
                let j : A.obj T.obj₁ → (A.map T.mor₂).hom.ker := fun x ↦
                  ⟨A.map T.mor₁ x, by
                    change (A.map T.mor₁ ≫ A.map T.mor₂) x = 0
                    rw [hcomp]
                    rfl⟩
                have hinj := (AddCommGrpCat.mono_iff_injective (A.map T.mor₁)).mp hmono
                exact Finite.of_injective j (fun x y h ↦ hinj (congrArg Subtype.val h))
              have : Finite ((Etale.cohomology AddCommGrpCat.{u + 1} C (1 : ℤ)).obj
                  ((DerivedCategory.singleFunctor
                    (Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj
                      (C.constantZMod r))) := hfin
              obtain ⟨e⟩ := Scheme.nonempty_sheafH_extDerivedIso C 1
              let E := (e.app (C.constantZMod r)).addCommGroupIsoToAddEquiv
              have : Finite ((DerivedCategory.singleFunctor
                  (Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) 0 ⋙
                    Etale.cohomology AddCommGrpCat.{u + 1} C (1 : ℤ)).obj
                      (C.constantZMod r)) := hfin
              exact Finite.of_injective E E.injective
            · have hzero : topologicalKrullDim C ≤ 0 := by
                have hlt : topologicalKrullDim C < 1 :=
                  lt_of_le_of_ne (IsCurve.krullDim_le_one (f := f)) hdim
                exact Order.le_of_lt_succ hlt
              have hvan := (zero_dimensional_etale_cohomology_rest k C f hzero
                (C.constantZMod r) (fun x ↦ AlgebraicClosure (C.residueField x)) C.algClosurePoint
                (fun x ↦ C.algClosurePoint_base x default)).1 1 (by decide)
              obtain ⟨e⟩ := Scheme.nonempty_sheafH_extDerivedIso C 1
              have hz : CategoryTheory.Limits.IsZero
                  ((Sheaf.functorH.{u + 1} C.smallEtaleTopology 1).obj
                  (C.constantZMod r)) :=
                CategoryTheory.Limits.IsZero.of_iso (AddCommGrpCat.isZero_iff_subsingleton.mpr hvan)
                  (e.app (C.constantZMod r))
              have : Subsingleton (Sheaf.H (C.constantZMod r) 1) :=
                AddCommGrpCat.subsingleton_of_isZero hz
              infer_instance
          exact finite_constantModSheaf_of_finite_constantZMod Λ C r 1
        · have := subsingleton_sheafH_constantModSheaf_of_one_lt_of_charP Λ f r q (by omega)
          infer_instance

/-- **`C₆` for `𝐅_r`.** Let `k ⊆ k'` be algebraically closed fields, `C` a smooth separated
connected curve over `k` and `r` a prime different from `char k`. For every cartesian square

```
C' --ι'--> C
|          |
f'         f
v          v
Spec k' -ι-> Spec k
```

the pullback map `Hᵠ(C, 𝐅_r) ⟶ Hᵠ(C', ι'^* 𝐅_r)` is bijective for every `q`. For `Λ = ℤ` and
the standard square this is `AlgebraicGeometry.bijective_cohomologyMap_constantZMod`. The
torsion hypothesis of the field `C₆` of `AlgebraicGeometry.IsCurve.Assertions` is replaced by
`(r : k) ≠ 0`.
(blueprint: theorem-cohomology-curves)
-/
theorem bijective_cohomologyMap_constantModSheaf_of_ne_zero [IsCurve f] [Smooth f]
    [ConnectedSpace C] (r : ℕ) [Fact r.Prime] (hr : (r : k) ≠ 0) (k' : Type u) [Field k']
    [IsAlgClosed k'] {C' : Scheme.{u}} {ι : Spec (.of k') ⟶ Spec (.of k)}
    {f' : C' ⟶ Spec (.of k')} {ι' : C' ⟶ C} (h : IsPullback ι' f' f ι) (q : ℕ) :
    Function.Bijective (Etale.cohomologyMap ι'
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        (Etale.constantModSheaf Λ C r)) q) :=
  by
    obtain ⟨a, rfl⟩ := Spec.map_surjective ι
    let : Algebra k k' := a.hom.toAlgebra
    let F := Etale.constantModSheaf Λ C r
    let F₀ := (Etale.upperStar (ModuleCat.{u + 1} Λ) (𝟙 C)).obj F
    have hF₀ : r • 𝟙 F₀ = 0 := by
      let T := Etale.upperStar (ModuleCat.{u + 1} Λ) (𝟙 C)
      change r • 𝟙 (T.obj F) = 0
      rw [← T.map_id, ← T.map_nsmul, Etale.nsmul_id_constantModSheaf Λ C r, T.map_zero]
    have hbase := bijective_constantModSheaf_standard_baseChange Λ (K := k') f r hr F₀ hF₀ q
    have ha : CommRingCat.ofHom (algebraMap k k') = a := rfl
    rw [ha] at hbase
    obtain ⟨b₁, b₂, hcomm⟩ := Etale.exists_addEquiv_cohomology_restrictionSquare Λ
      ι' (𝟙 C) h.isoPullback.inv (CategoryTheory.Limits.pullback.fst f (Spec.map a))
      (by rw [h.isoPullback_inv_fst, Category.comp_id]) F q
      (Etale.cohomologyMap_bijective _ _ _) (Etale.cohomologyMap_bijective _ _ _)
    constructor
    · intro x y hxy
      apply b₁.injective
      apply hbase.1
      rw [← hcomm x, ← hcomm y, hxy]
    · intro y
      obtain ⟨z, hz⟩ := hbase.2 (b₂ y)
      refine ⟨b₁.symm z, b₂.injective ?_⟩
      rw [hcomm, b₁.apply_symm_apply, hz]

/-- **`C₇` for `𝐅_r`.** Let `k ⊆ k'` be algebraically closed fields, `C` a smooth proper
connected curve over `k` and `r` an arbitrary prime. For every cartesian square

```
C' --ι'--> C
|          |
f'         f
v          v
Spec k' -ι-> Spec k
```

the pullback map `Hᵠ(C, 𝐅_r) ⟶ Hᵠ(C', ι'^* 𝐅_r)` is bijective for every `q`. For `r = char k`
this is the invariance of the Frobenius-fixed part of `H¹(C, 𝒪_C)` under the extension `k'/k`.
(blueprint: proposition-p-torsion-smooth-proper-curve--4)
-/
theorem bijective_cohomologyMap_constantModSheaf_of_isProper [IsCurve f] [Smooth f]
    [ConnectedSpace C] [IsProper f] (r : ℕ) [Fact r.Prime] (k' : Type u) [Field k']
    [IsAlgClosed k'] {C' : Scheme.{u}} {ι : Spec (.of k') ⟶ Spec (.of k)}
    {f' : C' ⟶ Spec (.of k')} {ι' : C' ⟶ C} (h : IsPullback ι' f' f ι) (q : ℕ) :
    Function.Bijective (Etale.cohomologyMap ι'
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        (Etale.constantModSheaf Λ C r)) q) :=
  by
    by_cases hq0 : q = 0
    · subst q
      exact proper_constant_base_change_zero f r k' h
    · by_cases hq1 : q = 1
      · subst q
        exact proper_constant_base_change_one f r k' h
      · apply proper_constant_base_change_higher f r k' h q
        omega


/-- **`C₈` for `𝐅_r`.** Let `C` be a smooth separated connected curve over an algebraically
closed field `k`, `a : W ⟶ C` an open immersion and `r` a prime. Then the restriction
`H²(C, 𝐅_r) ⟶ H²(W, a^* 𝐅_r)` is surjective: either `W = C`, or `W` is affine and
`H²(W, 𝐅_r) = 0`.
(blueprint: theorem-cohomology-curves)
-/
theorem surjective_cohomologyMap_constantModSheaf_two [IsCurve f] [Smooth f] [ConnectedSpace C]
    (r : ℕ) [Fact r.Prime] {W : Scheme.{u}} (a : W ⟶ C) [IsOpenImmersion a] :
    Function.Surjective (Etale.cohomologyMap a
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        (Etale.constantModSheaf Λ C r)) 2) :=
  by
    classical
    let F := (sheafCompose _
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        (Etale.constantModSheaf Λ C r)
    by_cases ha : Function.Surjective a
    · have : Surjective a := ⟨ha⟩
      have : IsIso a := (isIso_iff_isOpenImmersion_and_surjective a).mpr
        ⟨inferInstance, inferInstance⟩
      exact (Etale.cohomologyMap_bijective a F 2).surjective
    · have hW : IsAffine W := by
        have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian f
        have : IsRegular C := IsRegular.of_smooth f
        have : IrreducibleSpace C := IsRegular.irreducibleSpace C
        by_cases hdim : topologicalKrullDim C = 1
        · have : IsConnectedCurve f :=
            { krullDim_le_one := IsCurve.krullDim_le_one (f := f)
              connectedSpace := inferInstance
              krullDim_eq_one := hdim }
          obtain ⟨c, hc, hs, _hfin, _hcl⟩ :=
            IsConnectedCurve.exists_smooth_properCompactification f
          have := hc
          have := hs
          have := c.isProper
          have := c.isOpenImmersion
          let V := (a ≫ c.i).opensRange
          have hV : V ≠ ⊤ := by
            intro htop
            apply ha
            intro x
            have hx : c.i x ∈ V := by rw [htop]; trivial
            obtain ⟨w, hw⟩ := hx
            exact ⟨w, c.i.isOpenEmbedding.injective hw⟩
          have : IsAffine V := IsConnectedCurve.isAffine_of_ne_top c.g V hV
          let e : W ≅ (V : Scheme.{u}) :=
            IsOpenImmersion.isoOfRangeEq (a ≫ c.i) V.ι
              (by rw [Scheme.Opens.range_ι]; rfl)
          exact IsAffine.of_isIso e.hom
        · have h0 : topologicalKrullDim C ≤ 0 := by
            have h1 : topologicalKrullDim C < ((0 : ℕ) : WithBot ℕ∞) + 1 :=
              lt_of_le_of_ne (IsCurve.krullDim_le_one (f := f)) hdim
            exact ENat.WithBot.lt_add_one_iff.1 h1
          have : Subsingleton C := subsingleton_of_topologicalKrullDim_le_zero h0
          have : Subsingleton W := ⟨fun x y ↦ a.isOpenEmbedding.injective
            (Subsingleton.elim _ _)⟩
          infer_instance
      have : IsAffine W := hW
      have : IsNoetherian C := isNoetherian_of_locallyOfFiniteType f
      have : TopologicalSpace.NoetherianSpace W :=
        a.isOpenEmbedding.isInducing.noetherianSpace
      have : QuasiCompact a := ⟨fun U _ _ ↦
        TopologicalSpace.NoetherianSpace.isCompact _⟩
      have : IsCurve (a ≫ f) :=
        { krullDim_le_one := a.isOpenEmbedding.isInducing.topologicalKrullDim_le.trans
            (IsCurve.krullDim_le_one (f := f)) }
      have hF := Etale.isTorsion_constantModSheaf Λ C (Fact.out : r.Prime).pos
      have : Subsingleton (Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1} a).obj F) 2) :=
        subsingleton_sheafH_two_of_isAffine (a ≫ f) _ (Etale.isTorsion_upperStar a hF)
      exact fun y ↦ ⟨0, Subsingleton.elim _ _⟩

/-! ### The smooth-curve calculations -/

/-- **The smooth-curve calculations.** Let `C` be a smooth separated connected curve over an
algebraically closed field `k` and `n` a prime. The constant sheaf `𝐅_n` (read over `Λ` as
`Λ/nΛ`) satisfies

* `C₁` and `C₈`;
* `C₂` when `C` is affine, `C₅` and `C₇` when `C` is proper;
* `C₄` and `C₆` when `n ≠ char k` (part (a) of the blueprint statement), the finiteness in
  `C₄` and `C₅` when `Λ/nΛ` is finite;
* `C₃` when `n = char k` (part (b));

each in the form of the corresponding field of `AlgebraicGeometry.IsCurve.Assertions`, with the
coefficient hypotheses specialised to `𝐅_n` as in the lemmas above. The maps in `C₆`, `C₇`,
`C₈` are the pullback maps `AlgebraicGeometry.Etale.cohomologyMap` (part (c)).

Only the assertions are stated here; the explicit groups of part (a) are the curve estimates
`AlgebraicGeometry.Scheme.nonempty_addEquiv_sheafH_zero_constantZMod`,
`AlgebraicGeometry.IsCurve.nonempty_addEquiv_sheafH_constantZMod_one` and
`AlgebraicGeometry.IsCurve.nonempty_addEquiv_sheafH_constantZMod_two`, and their invariance
under algebraically closed extension is `AlgebraicGeometry.bijective_cohomologyMap_constantZMod`.
(blueprint: proposition-p-torsion-smooth-proper-curve--1)
-/
theorem constantModSheaf_curveCalculations [IsCurve f] [Smooth f] [ConnectedSpace C] (n : ℕ)
    [Fact n.Prime] :
    let F := (sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
      (Etale.constantModSheaf Λ C n)
    (∀ q, 2 < q → Subsingleton (Sheaf.H F q)) ∧
    (IsAffine C → ∀ q, 1 < q → Subsingleton (Sheaf.H F q)) ∧
    (CharP k n → ∀ q, 1 < q → Subsingleton (Sheaf.H F q)) ∧
    ((n : k) ≠ 0 → Finite (Λ ⧸ (Ideal.span {(n : Λ)} : Ideal Λ)) →
      ∀ q, Finite (Sheaf.H F q)) ∧
    (IsProper f → Finite (Λ ⧸ (Ideal.span {(n : Λ)} : Ideal Λ)) →
      ∀ q, Finite (Sheaf.H F q)) ∧
    ((n : k) ≠ 0 → ∀ (k' : Type u) [Field k'] [IsAlgClosed k'] {C' : Scheme.{u}}
      {ι : Spec (.of k') ⟶ Spec (.of k)} {f' : C' ⟶ Spec (.of k')} {ι' : C' ⟶ C},
      IsPullback ι' f' f ι → ∀ q, Function.Bijective (Etale.cohomologyMap ι' F q)) ∧
    (IsProper f → ∀ (k' : Type u) [Field k'] [IsAlgClosed k'] {C' : Scheme.{u}}
      {ι : Spec (.of k') ⟶ Spec (.of k)} {f' : C' ⟶ Spec (.of k')} {ι' : C' ⟶ C},
      IsPullback ι' f' f ι → ∀ q, Function.Bijective (Etale.cohomologyMap ι' F q)) ∧
    (∀ {W : Scheme.{u}} (a : W ⟶ C) [IsOpenImmersion a],
      Function.Surjective (Etale.cohomologyMap a F 2)) :=
  by
    dsimp
    exact ⟨subsingleton_sheafH_constantModSheaf_of_two_lt Λ f n,
    fun _ ↦ subsingleton_sheafH_constantModSheaf_of_one_lt_of_isAffine Λ f n,
    fun _ ↦ subsingleton_sheafH_constantModSheaf_of_one_lt_of_charP Λ f n,
    fun hn _ ↦ finite_sheafH_constantModSheaf_of_ne_zero Λ f n hn,
    fun _ _ ↦ finite_sheafH_constantModSheaf_of_isProper Λ f n,
    fun hn k' _ _ _ _ _ _ h ↦ bijective_cohomologyMap_constantModSheaf_of_ne_zero Λ f n hn k' h,
    fun _ k' _ _ _ _ _ _ h ↦ bijective_cohomologyMap_constantModSheaf_of_isProper Λ f n k' h,
    fun a _ ↦ surjective_cohomologyMap_constantModSheaf_two Λ f n a⟩

/-! ### The eight assertions on smooth curves -/

private theorem assertions_constantModSheaf_connected [IsCurve f] [Smooth f]
    [ConnectedSpace C] (r : ℕ) [Fact r.Prime]
    [Finite (Λ ⧸ (Ideal.span {(r : Λ)} : Ideal Λ))] :
    Assertions Λ f (Etale.constantModSheaf Λ C r) := by
  let F := Etale.constantModSheaf Λ C r
  let T := sheafCompose C.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  have : T.Additive := ⟨by intros; rfl⟩
  have hnonunit (hr : (r : k) = 0) : ¬ IsUnit (r : Γ(Spec (.of k), ⊤)) := by
    intro hu
    have hu' : IsUnit (r : k) := by
      simpa using hu.map
        (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.toMonoidHom
    exact hu'.ne_zero hr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact subsingleton_sheafH_constantModSheaf_of_two_lt Λ f r
  · intro _
    exact subsingleton_sheafH_constantModSheaf_of_one_lt_of_isAffine Λ f r
  · intro p _ _ hF q hq
    by_cases hrp : r = p
    · subst p
      exact subsingleton_sheafH_constantModSheaf_of_one_lt_of_charP Λ f r q hq
    · have hz := (Scheme.prime_annihilated_primary_cases Λ r F
        (Etale.nsmul_id_constantModSheaf Λ C r)).2 p hrp hF
      exact Sheaf.subsingleton_H_of_isZero (T.map_isZero hz) q
  · intro _ _ q
    by_cases hr : (r : k) ≠ 0
    · exact finite_sheafH_constantModSheaf_of_ne_zero Λ f r hr q
    · have := (prime_torsion_nonunit_cohomology Λ (k := k) (𝟙 C) r F
        (Etale.nsmul_id_constantModSheaf Λ C r) (hnonunit (not_ne_iff.mp hr)) q).1
      infer_instance
  · intro _ _
    exact finite_sheafH_constantModSheaf_of_isProper Λ f r
  · intro _ k' _ _ C' ι f' ι' h q
    by_cases hr : (r : k) ≠ 0
    · exact bijective_cohomologyMap_constantModSheaf_of_ne_zero Λ f r hr k' h q
    · obtain ⟨hs, ht⟩ := prime_torsion_nonunit_cohomology Λ (k := k) ι' r F
        (Etale.nsmul_id_constantModSheaf Λ C r) (hnonunit (not_ne_iff.mp hr)) q
      have := hs
      have := ht
      exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun y ↦ ⟨0, Subsingleton.elim _ _⟩⟩
  · intro _ k' _ _ C' ι f' ι' h q
    exact bijective_cohomologyMap_constantModSheaf_of_isProper Λ f r k' h q
  · intro W a _
    exact surjective_cohomologyMap_constantModSheaf_two Λ f r a

private theorem assertions_constantModSheaf_smooth [IsCurve f] [Smooth f]
    (r : ℕ) [Fact r.Prime] [Finite (Λ ⧸ (Ideal.span {(r : Λ)} : Ideal Λ))] :
    Assertions Λ f (Etale.constantModSheaf Λ C r) := by
  classical
  have : IsNoetherian C := isNoetherian_of_locallyOfFiniteType f
  choose x hx using ConnectedComponents.surjective_coe (α := C)
  let U (c : _root_.ConnectedComponents C) : C.Opens :=
    ⟨connectedComponent (x c), TopologicalSpace.NoetherianSpace.isOpen_connectedComponent _⟩
  have hcov (y : C) : ∃ c, y ∈ U c := by
    refine ⟨y, ?_⟩
    change y ∈ connectedComponent (x y)
    rw [ConnectedComponents.coe_eq_coe.mp (hx y)]
    exact mem_connectedComponent
  have hdisj : Pairwise (fun c d ↦ Disjoint (U c : Set C) (U d)) := by
    intro c d hcd
    refine Set.disjoint_left.mpr fun y (hyc : y ∈ connectedComponent (x c))
      (hyd : y ∈ connectedComponent (x d)) ↦ hcd ?_
    rw [← hx c, ← hx d, ConnectedComponents.coe_eq_coe,
      connectedComponent_eq hyc, connectedComponent_eq hyd]
  apply assertions_constant_of_isClopen Λ f
    (ModuleCat.of Λ (Λ ⧸ (Ideal.span {(r : Λ)} : Ideal Λ))) U
    (fun _ ↦ isClosed_connectedComponent) hdisj hcov
  intro c
  have : ConnectedSpace (U c) :=
    isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  have : IsCurve ((U c).ι ≫ f) :=
    { krullDim_le_one := (topologicalKrullDim_subspace_le C (U c)).trans
        (IsCurve.krullDim_le_one (f := f)) }
  exact assertions_constantModSheaf_connected Λ ((U c).ι ≫ f) r

/-- **The eight assertions for `𝐅_ℓ`, `ℓ ≠ char k`, on a smooth curve.** Let `k` be
algebraically closed, `C` a smooth separated `k`-scheme of finite type of dimension at most
one (not necessarily connected) and `ℓ` a prime different from `char k`. Then the constant sheaf
`𝐅_ℓ` (read over `Λ` as `Λ/ℓΛ`, assumed finite) satisfies all eight assertions
`AlgebraicGeometry.IsCurve.Assertions`; their maps are the pullback maps
`AlgebraicGeometry.Etale.cohomologyMap`. The proof goes through the Kummer sequence, the
compactification of `C` and purity for the boundary points.
(blueprint: theorem-cohomology-curves)
-/
theorem assertions_constantModSheaf_of_ne_zero [IsCurve f] [Smooth f] (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : (ℓ : k) ≠ 0) [Finite (Λ ⧸ (Ideal.span {(ℓ : Λ)} : Ideal Λ))] :
    IsCurve.Assertions Λ f (Etale.constantModSheaf Λ C ℓ) :=
  by
    have _ := hℓ
    exact assertions_constantModSheaf_smooth Λ f ℓ

/-- **The eight assertions for `𝐅_p`, `p = char k`, on a smooth curve.** Let `k` be
algebraically closed of characteristic `p > 0` and `C` a smooth separated `k`-scheme of finite
type of dimension at most one (not necessarily connected). Then the constant sheaf `𝐅_p` (read
over `Λ` as `Λ/pΛ`, assumed finite) satisfies all eight assertions
`AlgebraicGeometry.IsCurve.Assertions`
(`C₄` and `C₆` hold since their torsion hypothesis forces the sheaf to vanish). The proof goes
through the Artin–Schreier sequence `0 → 𝐅_p → 𝒪_C → 𝒪_C → 0`; for proper `C` the invariance
`C₇` comes from that of the kernel of `F - 1` on `H¹(C, 𝒪_C)` (this description of the map is
not stated).
(blueprint: theorem-cohomology-curves)
-/
theorem assertions_constantModSheaf_of_charP [IsCurve f] [Smooth f] (p : ℕ) [Fact p.Prime]
    [CharP k p] [Finite (Λ ⧸ (Ideal.span {(p : Λ)} : Ideal Λ))] :
    IsCurve.Assertions Λ f (Etale.constantModSheaf Λ C p) :=
  assertions_constantModSheaf_smooth Λ f p

end IsCurve

end AlgebraicGeometry
