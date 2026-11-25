/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.CechComparisonSystem
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.CechAcyclic
import Mathlib.Algebra.FiveLemma

/-! # Affine degeneration of normalized Čech comparisons

Source: Stacks Project, Tags 01ET and 01XD.
(blueprint: lem-pc-cech-comparison-affine)
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance] cohomologyHasSheafify cohomologyHasExt

private theorem comparison_bijective
    {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    (hU : ∀ (k : ℕ) (y : Fin (k + 1) → ι), IsAffineOpen (⨅ l, U (y l)))
    (hcover : iSup U = ⊤) (c : CechComparisonSystem U hcover) (q : ℕ) :
    ∀ (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}),
      cechAcyclicOnAffines X F → Function.Bijective ((c.comparison q).app F) := by
  induction q with
  | zero =>
    intro F hF
    rw [c.zero]
    exact (asIso (((TopCat.Sheaf.cechCohomologyZeroIso U hcover).inv ≫
      (Sheaf.functorHZeroIso.{u} (Opens.grothendieckTopology X) isTerminalTop).inv).app F)
        ).addCommGroupIsoToAddEquiv.bijective
  | succ q ih =>
    intro F hF
    let T := ObjectProperty.injectiveShortComplex F
    have hT : T.ShortExact := ObjectProperty.shortExact_injectiveShortComplex F
    have hg (k : ℕ) (y : Fin (k + 1) → ι) :
        Function.Surjective (T.g.hom.app (op (⨅ l, U (y l)))) :=
      surjective_app_of_cechAcyclicOnAffines hT hF (hU k y)
    have hp := cechAcyclicOnAffines_under_cokernel hF
    apply AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact
      ((TopCat.Sheaf.cechCohomologyFunctor U q).map T.g).hom
      (TopCat.Sheaf.cechδ U hT hg q).hom
      ((Sheaf.functorH.{u} (Opens.grothendieckTopology X) q).map T.g).hom
      (Sheaf.functorHδ.{u} hT q).hom
      ((c.comparison q).app T.X₂).hom
      ((c.comparison q).app T.X₃).hom
      ((c.comparison (q + 1)).app T.X₁).hom
    · exact congrArg AddCommGrpCat.Hom.hom ((c.comparison q).naturality T.g).symm
    · exact congrArg AddCommGrpCat.Hom.hom (c.connecting T hT hg q).symm
    · intro x
      exact TopCat.Sheaf.cechδ_eq_zero_iff U hT hg q x
    · intro x
      exact Sheaf.functorHδ_eq_zero_iff.{u} hT q x
    · exact (ih T.X₂ hp.1).2
    · exact ih T.X₃ hp.2
    · exact TopCat.Sheaf.cechδ_surjective U hT hg q
    · exact Sheaf.functorHδ_surjective.{u} hT q

private theorem comparison_smul
    {R : Type u} [CommRing R] {X : Scheme.{u}} {ι : Type u}
    (f : X ⟶ Spec (.of R)) (U : ι → X.Opens) (hcover : iSup U = ⊤)
    (c : CechComparisonSystem U hcover) (M : X.Modules) (q : ℕ)
    (r : R) (x : (cechOver f U M).homology q) :
    c.overMap f M q (r • x) = r • c.overMap f M q x := by
  let a := (((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom) r
  let ψ := (SheafOfModules.toSheaf X.ringCatSheaf).map (M.smulHom a)
  have hw : Functor.whiskerRight (r • 𝟙 (presheafOver f M))
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) ≫ (presheafOverForgetIso f M).hom =
      (presheafOverForgetIso f M).hom ≫ ψ.hom := by
    ext V y
    rfl
  have key : HomologicalComplex.homologyMap ((TopCat.Presheaf.cechComplex U).map
      (Functor.whiskerRight (r • 𝟙 (presheafOver f M))
        (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}))) q ≫
      HomologicalComplex.homologyMap ((TopCat.Presheaf.cechComplex U).map
        (presheafOverForgetIso f M).hom) q =
      HomologicalComplex.homologyMap ((TopCat.Presheaf.cechComplex U).map
        (presheafOverForgetIso f M).hom) q ≫
      HomologicalComplex.homologyMap ((TopCat.Presheaf.cechComplex U).map ψ.hom) q := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      ← Functor.map_comp, ← Functor.map_comp, hw]
  have he : cechOverHomologyAddEquiv f U M q (r • x) =
      (TopCat.Sheaf.cechCohomologyFunctor U q).map ψ
        (cechOverHomologyAddEquiv f U M q x) := by
    change HomologicalComplex.homologyMap ((TopCat.Presheaf.cechComplex U).map
        (presheafOverForgetIso f M).hom) q
        ((TopCat.Presheaf.cechComplexFunctorHomologyIso U (presheafOver f M) q).hom
          (r • x)) =
      HomologicalComplex.homologyMap ((TopCat.Presheaf.cechComplex U).map ψ.hom) q
        (HomologicalComplex.homologyMap ((TopCat.Presheaf.cechComplex U).map
          (presheafOverForgetIso f M).hom) q
          ((TopCat.Presheaf.cechComplexFunctorHomologyIso U (presheafOver f M) q).hom x))
    rw [TopCat.Presheaf.cechComplexFunctorHomologyIso_hom_smul]
    exact ConcreteCategory.congr_hom key _
  have hn := ConcreteCategory.congr_hom ((c.comparison q).naturality ψ)
    (cechOverHomologyAddEquiv f U M q x)
  change (c.comparison q).app _ (cechOverHomologyAddEquiv f U M q (r • x)) = _
  rw [he]
  exact hn

/-- A normalized comparison is bijective and linear on an affine-intersection cover.
It is essential that the system is normalized and commutes with connecting maps;
this assertion would be false for an arbitrary additive comparison.

Source: Stacks Project, Tags 01ET and 01XD.
(blueprint: lem-pc-cech-comparison-affine)

Proof: Work on the class of abelian sheaves acyclic on affine opens. It contains
quasi-coherent module sheaves and injectives and is stable under taking the cokernel
of an embedding into an injective. Such embeddings give sectionwise-surjective
short exact sequences on every affine tuple intersection. In degree zero the
normalization identifies the comparison with the gluing and Ext-section isomorphisms.
Inductively use the exact Čech and sheaf cohomology sequences for the embedding into
an injective. Both higher cohomologies of the injective vanish, and the connecting-map
law identifies the induced cokernel maps; hence the comparison in the next degree is
bijective. For linearity, naturality of comparison with respect to multiplication by
any global function identifies its action on Čech homology with its Ext cohomology
action. The scalar-restriction homology transport respects that multiplication,
as in `cechComplexFunctorHomologyIso_hom_smul`. Restrict along the homomorphism induced by
f to obtain R-linearity. All tuple intersections are affine without any assumption
that X or f is separated. Infinite covers cause no change to the acyclicity argument;
empty covers imply an empty scheme, where both sides are zero. -/
theorem cechComparison_affine_bijective_linear
    {R : Type u} [CommRing R] {X : Scheme.{u}} {ι : Type u}
    (f : X ⟶ Spec (.of R)) (U : ι → X.Opens)
    (hU : ∀ (k : ℕ) (y : Fin (k + 1) → ι), IsAffineOpen (⨅ l, U (y l)))
    (hcover : iSup U = ⊤) (c : CechComparisonSystem U hcover)
    (M : X.Modules) [M.IsQuasicoherent] (q : ℕ) :
    Function.Bijective (c.overMap f M q) ∧
      ∀ (r : R) (x : (cechOver f U M).homology q),
        c.overMap f M q (r • x) = r • c.overMap f M q x := by
  refine ⟨(comparison_bijective U hU hcover c q _
    (cechAcyclicOnAffines_of_isQuasicoherent M)).comp
      (cechOverHomologyAddEquiv f U M q).bijective, ?_⟩
  exact comparison_smul f U hcover c M q

end AlgebraicGeometry.Scheme.Modules
