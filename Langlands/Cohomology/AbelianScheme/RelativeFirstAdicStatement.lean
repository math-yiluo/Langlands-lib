import Langlands.AbelianScheme.Tate.PrimeTestScheme
import Langlands.Cohomology.AbelianScheme.RelativeAdicMultiplicationStatement
import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.CategoryTheory.Sites.SheafHom

/-! # Compatibility of the relative first cohomology character isomorphisms -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Langlands.Geometry EtaleDerivedSections
open Langlands.GroupScheme.Tate
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Cohomology.AbelianRelativeEtale

variable {S : Scheme.{0}} (A : Langlands.AbelianScheme S) (p : ℕ) [Fact p.Prime]

local notation "R" => ℤ_[p]

private abbrev forgetEtale : S.Etale ⥤ Over S :=
  MorphismProperty.Over.forget (@Etale) ⊤ S

private def torsionSections (r : ℕ) : S.Etaleᵒᵖ ⥤ ModuleCat R where
  obj U := ModuleCat.of R (Level A.toGrp (forgetEtale.obj U.unop) (p ^ r))
  map a := ModuleCat.ofHom (PrimeAdic.levelTestRestrict A.toGrp p (forgetEtale.map a.unop) r)
  map_id U := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply toSection_injective
    apply Additive.toMul.injective
    change (forgetEtale.map (𝟙 U).unop) ≫ Additive.toMul (toSection A.toGrp _ (p ^ r) x) = _
    rw [unop_id, (forgetEtale (S := S)).map_id, Category.id_comp]
    rfl
  map_comp a b := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply toSection_injective
    apply Additive.toMul.injective
    change (forgetEtale.map (a ≫ b).unop) ≫ Additive.toMul (toSection A.toGrp _ (p ^ r) x) =
      forgetEtale.map b.unop ≫ Additive.toMul (toSection A.toGrp _ (p ^ r)
        (levelRestrict A.toGrp (forgetEtale.map a.unop) (p ^ r) x))
    rw [unop_comp, Functor.map_comp, toSection_levelRestrict, Category.assoc]

/-- Prime-power torsion as a sheaf of modules over the fixed ring of p-adic integers. -/
def primePowerTorsionSheaf (r : ℕ) : ModuleSheaf S R :=
  (presheafToSheaf S.smallEtaleTopology (ModuleCat R)).obj (torsionSections A p r)

/-- The map from exponent `s` to exponent `r` comes from multiplication by
`p ^ (s - r)` on torsion points. -/
def primePowerTorsionTransition {r s : ℕ} (h : r ≤ s) :
    primePowerTorsionSheaf A p s ⟶ primePowerTorsionSheaf A p r :=
  (presheafToSheaf S.smallEtaleTopology (ModuleCat R)).map
    { app := fun U => ModuleCat.ofHom
        { toAddHom := transition A.toGrp (forgetEtale.obj U.unop) (pow_dvd_pow p h)
          map_smul' := PrimeAdic.transition_smul A.toGrp (forgetEtale.obj U.unop) p h }
      naturality := by
        intro U V a
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact (levelRestrict_transition A.toGrp (forgetEtale.map a.unop) (pow_dvd_pow p h) x).symm }

private abbrev constantSystem (X : Scheme.{0}) : ℕᵒᵖ ⥤ ModuleSheaf X R :=
  EtaleAdicSystem.ellPowerConstantSystem X p (ModuleCat.of R R)

private abbrev characterValues (r : ℕ) : S.Etaleᵒᵖ ⥤ Type 1 :=
  presheafHom (primePowerTorsionSheaf A p r).obj ((constantSystem p S).obj (op r)).obj

private instance characterValues_addCommGroup (r : ℕ) (U : S.Etaleᵒᵖ) :
    AddCommGroup ((characterValues A p r).obj U) :=
  inferInstanceAs (AddCommGroup
    ((Over.forget U.unop).op ⋙ (primePowerTorsionSheaf A p r).obj ⟶
      (Over.forget U.unop).op ⋙ ((constantSystem p S).obj (op r)).obj))

private instance characterValues_module (r : ℕ) (U : S.Etaleᵒᵖ) :
    Module R ((characterValues A p r).obj U) :=
  inferInstanceAs (Module R
    ((Over.forget U.unop).op ⋙ (primePowerTorsionSheaf A p r).obj ⟶
      (Over.forget U.unop).op ⋙ ((constantSystem p S).obj (op r)).obj))

/-- The module of characters on each étale slice is the internal Hom from
prime-power torsion to the finite constant coefficient sheaf. -/
def primePowerCharacterPresheaf (r : ℕ) : S.Etaleᵒᵖ ⥤ ModuleCat.{1} R where
  obj U := ModuleCat.of R ((characterValues A p r).obj U)
  map a := ModuleCat.ofHom
    { toFun := (characterValues A p r).map a
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  map_id U := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (characterValues A p r).map_id_apply U x
  map_comp a b := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (characterValues A p r).map_comp_apply a b x

/-- The prime-power character presheaf satisfies the sheaf condition. -/
theorem primePowerCharacterPresheaf_isSheaf (r : ℕ) :
    Presheaf.IsSheaf S.smallEtaleTopology (primePowerCharacterPresheaf A p r) := by
  let : ReflectsLimitsOfSize.{0, 1} (forget (ModuleCat.{1} R)) :=
    reflectsLimitsOfSize_of_univLE.{1, 1} _
  refine Presheaf.isSheaf_of_isSheaf_comp S.smallEtaleTopology
    (primePowerCharacterPresheaf A p r) (forget (ModuleCat.{1} R)) ?_
  change Presheaf.IsSheaf S.smallEtaleTopology (characterValues A p r)
  exact ((constantSystem p S).obj (op r)).property.hom (primePowerTorsionSheaf A p r).obj

private abbrev liftedFirstCohomology : ℕᵒᵖ ⥤ (S.Etaleᵒᵖ ⥤ ModuleCat.{1} R) :=
  relativeAdicCohomologySystem p A.X.hom 1 ⋙ sheafToPresheaf S.smallEtaleTopology (ModuleCat R) ⋙
    (Functor.whiskeringRight S.Etaleᵒᵖ _ _).obj (ModuleCat.uliftFunctor.{1} R)

/-- The relative character isomorphisms can be chosen compatibly with
coefficient reduction and the quotient-power maps on torsion. -/
def RelativeFirstAdicCharacterCompatibilityStatement : Prop :=
  IsUnit (p : Γ(S, ⊤)) →
    ∃ e : ∀ r : ℕ, (liftedFirstCohomology A p).obj (op r) ≅ primePowerCharacterPresheaf A p r,
      ∀ (r s : ℕ) (h : r ≤ s) (U : S.Etaleᵒᵖ)
        (x : ((liftedFirstCohomology A p).obj (op s)).obj U),
        (e s).hom.app U x ≫
            Functor.whiskerLeft (Over.forget U.unop).op
              ((constantSystem p S).map (homOfLE h).op).hom =
          Functor.whiskerLeft (Over.forget U.unop).op (primePowerTorsionTransition A p h).hom ≫
            (e r).hom.app U (((liftedFirstCohomology A p).map (homOfLE h).op).app U x)

end Langlands.Cohomology.AbelianRelativeEtale
