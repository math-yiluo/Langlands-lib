import Langlands.AlgebraicGeometry.AffineCechDeRham
import Langlands.AlgebraicGeometry.RelativeDifferentialsAffineSectionGenerators

/-! # Kähler differentials of the actual affine section rings over the base ring -/

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.AffineCechDeRham

section ScalarImage

variable {K L A : Type u} [CommRing K] [CommRing L] [CommRing A]
  [Algebra K A] [Algebra L A]

private def changeBaseDerivation {M : Type u} [AddCommGroup M] [Module A M]
    [Module K M] [Module L M] [IsScalarTower L A M]
    (d : Derivation K A M) (h : ∀ l : L, d (algebraMap L A l) = 0) : Derivation L A M := by
  refine Derivation.mk' { d.toAddMonoidHom with map_smul' := fun l a => ?_ } d.leibniz
  change d (l • a) = l • d a
  rw [Algebra.smul_def l a, d.leibniz, h, smul_zero, add_zero, IsScalarTower.algebraMap_smul A]

private def changeBaseMap (h : Set.range (algebraMap L A) ⊆ Set.range (algebraMap K A)) :
    Ω[A⁄L] →ₗ[A] Ω[A⁄K] := by
  exact (changeBaseDerivation (KaehlerDifferential.D K A) (fun l => by
    obtain ⟨k, hk⟩ := h ⟨l, rfl⟩
    rw [← hk, Derivation.map_algebraMap])).liftKaehlerDifferential

@[simp]
private lemma changeBaseMap_D (h : Set.range (algebraMap L A) ⊆ Set.range (algebraMap K A)) (a : A) :
    changeBaseMap h (KaehlerDifferential.D L A a) = KaehlerDifferential.D K A a := by
  simp [changeBaseMap, changeBaseDerivation]

private def sameImageEquiv (h : Set.range (algebraMap K A) = Set.range (algebraMap L A)) :
    Ω[A⁄K] ≃ₗ[A] Ω[A⁄L] :=
  LinearEquiv.ofLinearMap (changeBaseMap h.le) (changeBaseMap h.ge)
    (Derivation.liftKaehlerDifferential_unique _ _ (by ext a; simp))
    (Derivation.liftKaehlerDifferential_unique _ _ (by ext a; simp))

@[simp]
private lemma sameImageEquiv_D (h : Set.range (algebraMap K A) = Set.range (algebraMap L A)) (a : A) :
    sameImageEquiv h (KaehlerDifferential.D K A a) = KaehlerDifferential.D L A a :=
  changeBaseMap_D h.le a

end ScalarImage

open Langlands.Scheme

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of R))

private abbrev baseSections (R : Type u) [CommRing R] := Γ(Spec (CommRingCat.of R), ⊤)

private abbrev ringOn (W : X.Opens) := (sectionAlgebras f).obj (op W)

private lemma baseMap_range (W : X.Opens) :
    letI : Algebra (baseSections R) (ringOn f W) := (f.appLE ⊤ W le_top).hom.toAlgebra
    Set.range (algebraMap R (ringOn f W)) = Set.range (algebraMap (baseSections R) (ringOn f W)) := by
  let C := Scheme.ΓSpecIso (CommRingCat.of R)
  let : Algebra (baseSections R) (ringOn f W) := (f.appLE ⊤ W le_top).hom.toAlgebra
  change Set.range ((f.appLE ⊤ W le_top).hom ∘ C.inv.hom) = Set.range (f.appLE ⊤ W le_top).hom
  rw [Set.range_comp, (ConcreteCategory.bijective_of_isIso C.inv).2.range_eq, Set.image_univ]

local instance (W : X.Opens) : Module (ringOn f W) Γ(relativeDifferentials f, W) :=
  inferInstanceAs (Module Γ(X, W) Γ(relativeDifferentials f, W))

/-- The affine algebraic one-forms over `R` identify with the actual
sections of the relative differential sheaf on that open. -/
def oneFormsSectionsEquiv (W : X.Opens) (hW : IsAffineOpen W) :
    Ω[(ringOn f W)⁄R] ≃ₗ[ringOn f W] Γ(relativeDifferentials f, W) := by
  letI : Algebra (baseSections R) (ringOn f W) := (f.appLE ⊤ W le_top).hom.toAlgebra
  let E : Ω[(ringOn f W)⁄(baseSections R)] ≃ₗ[ringOn f W] Γ(relativeDifferentials f, W) :=
    (relativeDifferentialsSectionsIso f (isAffineOpen_top _) hW le_top).toLinearEquiv.symm
  exact (sameImageEquiv (baseMap_range f W)).trans E

@[simp]
lemma oneFormsSectionsEquiv_D (W : X.Opens) (hW : IsAffineOpen W) (a : ringOn f W) :
    oneFormsSectionsEquiv f W hW (KaehlerDifferential.D R _ a) =
      (relativeDifferentialsDerivation f).app W a := by
  let : Algebra (baseSections R) (ringOn f W) := (f.appLE ⊤ W le_top).hom.toAlgebra
  exact (congrArg ((relativeDifferentialsSectionsIso f (isAffineOpen_top _) hW le_top).toLinearEquiv.symm)
      (sameImageEquiv_D (baseMap_range f W) a)).trans
    (relativeDifferentialsSectionsIso_inv_D f (isAffineOpen_top _) hW le_top a)

/-- The affine comparison identifies the restriction maps of algebraic
one-forms with the actual restrictions of differential sections. -/
lemma oneFormsSectionsEquiv_restrict {W W' : X.Opens} (hW : IsAffineOpen W)
    (hW' : IsAffineOpen W') (e : W' ≤ W) (ω : Ω[(ringOn f W)⁄R]) :
    oneFormsSectionsEquiv f W' hW'
        (RelativeForms.mapOne ((sectionAlgebras f).map (homOfLE e).op).hom ω) =
      (relativeDifferentials f).presheaf.map (homOfLE e).op (oneFormsSectionsEquiv f W hW ω) := by
  let ρ := ((sectionAlgebras f).map (homOfLE e).op).hom
  obtain ⟨t, rfl⟩ := KaehlerDifferential.tensorProductTo_surjective R (ringOn f W) ω
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
    rw [Derivation.tensorProductTo_tmul, (RelativeForms.mapOne ρ).map_smulₛₗ,
      RelativeForms.mapOne_d, map_smul, oneFormsSectionsEquiv_D, map_smul, oneFormsSectionsEquiv_D]
    let d := relativeDifferentialsDerivation f
    let P := (relativeDifferentials f).presheaf
    change X.presheaf.map (homOfLE e).op (a : Γ(X, W)) •
        d.app W' (X.presheaf.map (homOfLE e).op (b : Γ(X, W))) =
      P.map (homOfLE e).op ((a : Γ(X, W)) • d.app W b)
    rw [d.app_restrict]
    exact (PresheafOfModules.map_smul (relativeDifferentials f).val
      (homOfLE e).op (a : Γ(X, W)) _).symm
  | add x y hx hy =>
    simpa only [map_add] using congrArg₂ (· + ·) hx hy

end Langlands.AlgebraicGeometry.AffineCechDeRham
