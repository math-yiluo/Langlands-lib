import Langlands.AlgebraicGeometry.Picard.ElementaryArtinianResidueCoefficientNaturality
import Langlands.AlgebraicGeometry.Modules.BasisHomGluing
import Langlands.AlgebraicGeometry.Modules.AffineBaseSections

/-! # The ideal coordinate square from lifted-section formulas -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard.ElementaryArtinianIdealCohomology

open StructureKernelModule Langlands.Scheme.Modules
  Langlands.Scheme.Modules.BasisHomGluing
  Langlands.AlgebraicGeometry.Modules.AdicStalkQuotient

variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) [IsLocalRing S]
  (ι : Type u) {X Y : Over (Spec (CommRingCat.of R))}

/-- Transport the prescribed product coefficient map through chosen ideal coordinates. -/
def idealCoordinateCoefficient
    (eX : ideal φ X ≅ ∏ᶜ fun _ : ι => residueModule φ X)
    (eY : ideal φ Y ≅ ∏ᶜ fun _ : ι => residueModule φ Y) (f : Y ⟶ X) :
    ideal φ X ⟶ (Scheme.Modules.pushforward f.left).obj (ideal φ Y) :=
  eX.hom ≫ residueProductCoefficient φ ι f ≫
    (Scheme.Modules.pushforward f.left).map eY.inv

/-- Transported coefficients have the required coordinate square. -/
@[reassoc]
lemma idealCoordinateCoefficient_π
    (eX : ideal φ X ≅ ∏ᶜ fun _ : ι => residueModule φ X)
    (eY : ideal φ Y ≅ ∏ᶜ fun _ : ι => residueModule φ Y) (f : Y ⟶ X) (j : ι) :
    idealCoordinateCoefficient φ ι eX eY f ≫
        (Scheme.Modules.pushforward f.left).map
          (eY.hom ≫ Pi.π (fun _ : ι => residueModule φ Y) j) =
      eX.hom ≫ Pi.π (fun _ : ι => residueModule φ X) j ≫ residueCoefficient φ f := by
  simp only [idealCoordinateCoefficient, Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp,
    residueProductCoefficient_π]

omit [IsLocalRing S] in
/-- The actual ideal inclusions determine a compatible coefficient map uniquely. -/
lemma compatible_unique (f : Y ⟶ X)
    (k l : ideal φ X ⟶ (Scheme.Modules.pushforward f.left).obj (ideal φ Y))
    (hk : Compatible φ f k) (hl : Compatible φ f l) : k = l := by
  apply Scheme.Modules.hom_ext
  intro U
  ext a
  apply Subtype.ext
  exact congrArg
    (fun m : ideal φ X ⟶
        (Scheme.Modules.pushforward f.left).obj (SheafOfModules.unit Y.left.ringCatSheaf) =>
      Scheme.Modules.Hom.app m U a) (hk.trans hl.symm)

/-- Every compatible ideal map has the coordinate square of a compatible transported map. -/
lemma coordinate_square_of_compatible
    (eX : ideal φ X ≅ ∏ᶜ fun _ : ι => residueModule φ X)
    (eY : ideal φ Y ≅ ∏ᶜ fun _ : ι => residueModule φ Y) (f : Y ⟶ X)
    (hc : Compatible φ f (idealCoordinateCoefficient φ ι eX eY f))
    (k : ideal φ X ⟶ (Scheme.Modules.pushforward f.left).obj (ideal φ Y))
    (hk : Compatible φ f k) (j : ι) :
    k ≫ (Scheme.Modules.pushforward f.left).map
        (eY.hom ≫ Pi.π (fun _ : ι => residueModule φ Y) j) =
      eX.hom ≫ Pi.π (fun _ : ι => residueModule φ X) j ≫ residueCoefficient φ f := by
  rw [compatible_unique φ f k (idealCoordinateCoefficient φ ι eX eY f) hk hc]
  exact idealCoordinateCoefficient_π φ ι eX eY f j

/-- Residue sections lift on every affine open when the original ring map is surjective. -/
lemma residueι_app_surjective (hφ : Function.Surjective φ)
    (U : X.left.Opens) (hU : IsAffineOpen U) :
    Function.Surjective ((residueι φ X).app U) := by
  let : IsClosedImmersion (residueBaseMap φ) :=
    IsClosedImmersion.spec_of_surjective _ (residue_surjective.comp hφ)
  have : IsClosedImmersion (residueι φ X) := by
    dsimp only [residueι]
    infer_instance
  exact (residueι φ X).app_surjective U hU

private lemma appLE_congr {T Z : Scheme.{u}} {p q : Z ⟶ T} (h : p = q)
    (U : T.Opens) (V : Z.Opens) (e : V ≤ p ⁻¹ᵁ U) :
    p.appLE U V e = q.appLE U V (h ▸ e) := by
  cases h
  rfl

private lemma baseSectionHom_naturality (f : Y ⟶ X) (U : X.left.Opens) (a : R) :
    f.left.app U (baseSectionHom X.hom U a) =
      baseSectionHom Y.hom (f.left ⁻¹ᵁ U) a := by
  have hh : X.hom.appLE ⊤ U le_top ≫ f.left.app U =
      Y.hom.appLE ⊤ (f.left ⁻¹ᵁ U) le_top := by
    rw [f.left.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    exact appLE_congr f.w _ _ _
  exact ConcreteCategory.congr_hom hh ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a)

variable [Fintype ι]

/-- Common inverse coordinate formulas imply compatibility with the actual ideal inclusions. -/
lemma idealCoordinateCoefficient_compatible
    (eX : ideal φ X ≅ ∏ᶜ fun _ : ι => residueModule φ X)
    (eY : ideal φ Y ≅ ∏ᶜ fun _ : ι => residueModule φ Y)
    (v : ι → R)
    (hX : ∀ (U : X.left.Opens), IsAffineOpen U →
      ∀ (r : ι → Γ(X.left, U)) (s : Γ(∏ᶜ fun _ : ι => residueModule φ X, U)),
        (∀ j, (Pi.π (fun _ : ι => residueModule φ X) j).app U s =
          (residueι φ X).app U (r j)) →
        ((eX.inv).app U s).val = ∑ j, baseSectionHom X.hom U (v j) * r j)
    (hY : ∀ (U : Y.left.Opens)
      (r : ι → Γ(Y.left, U)) (s : Γ(∏ᶜ fun _ : ι => residueModule φ Y, U)),
        (∀ j, (Pi.π (fun _ : ι => residueModule φ Y) j).app U s =
          (residueι φ Y).app U (r j)) →
        ((eY.inv).app U s).val = ∑ j, baseSectionHom Y.hom U (v j) * r j)
    (hSurj : ∀ (U : X.left.Opens), IsAffineOpen U →
      Function.Surjective ((residueι φ X).app U))
    (f : Y ⟶ X) :
    Compatible φ f (idealCoordinateCoefficient φ ι eX eY f) := by
  classical
  apply hom_ext_of_basis (fun _ _ hx => exists_isAffineOpen_mem_and_subset hx)
  intro U hU
  ext a
  let s := (eX.hom).app U a
  choose r hr using fun j => hSurj U hU ((Pi.π (fun _ : ι => residueModule φ X) j).app U s)
  have hs : ∀ j, (Pi.π (fun _ : ι => residueModule φ X) j).app U s =
      (residueι φ X).app U (r j) := fun j => (hr j).symm
  let t := (residueProductCoefficient φ ι f).app U s
  have ht : ∀ j, (Pi.π (fun _ : ι => residueModule φ Y) j).app (f.left ⁻¹ᵁ U) t =
      (residueι φ Y).app (f.left ⁻¹ᵁ U) (f.left.app U (r j)) := by
    intro j
    have hp := congrArg
      (fun m : (∏ᶜ fun _ : ι => residueModule φ X) ⟶
          (Scheme.Modules.pushforward f.left).obj (residueModule φ Y) =>
        Scheme.Modules.Hom.app m U s)
      (residueProductCoefficient_π φ ι f j)
    change (Pi.π (fun _ : ι => residueModule φ Y) j).app (f.left ⁻¹ᵁ U) t =
      (residueCoefficient φ f).app U
        ((Pi.π (fun _ : ι => residueModule φ X) j).app U s) at hp
    rw [hs j, residueCoefficient_app_lift] at hp
    exact hp
  have ha : ((eX.inv).app U s).val = a.val := by
    have hh := congrArg
      (fun m : ideal φ X ⟶ ideal φ X => Scheme.Modules.Hom.app m U a)
      eX.hom_inv_id
    exact congrArg Subtype.val hh
  change ((eY.inv).app (f.left ⁻¹ᵁ U) t).val = f.left.app U a.val
  rw [hY _ (fun j => f.left.app U (r j)) t ht, ← ha, hX U hU r s hs]
  simp only [map_sum, map_mul, baseSectionHom_naturality]

end Langlands.AlgebraicGeometry.Picard.ElementaryArtinianIdealCohomology
