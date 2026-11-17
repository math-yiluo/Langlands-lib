import Langlands.Geometry.FormalGroup.RationalSectionComposition

/-! # Bilinear composition and identities for actual rational sections -/

noncomputable section
universe u v
namespace Langlands.FormalGroup.ModuleLaw
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
attribute [local instance] coefficientAlgebra coefficientScalarTower

private theorem eq_of_local_lifts {X : TopCat.{v}}
    {A B : TopCat.Presheaf (Type v) X} (e : A ⟶ B)
    [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) e]
    (H : TopCat.Sheaf (Type v) X) {U : Opens X} (b : B.obj (op U))
    (s t : H.obj.obj (op U))
    (h : ∀ (V : Opens X) (i : V ⟶ U) (a : A.obj (op V)),
      e.app (op V) a = B.map i.op b → H.obj.map i.op s = H.obj.map i.op t) : s = t := by
  have hs : Presieve.IsSheaf (Opens.grothendieckTopology X) H.obj :=
    (isSheaf_iff_isSheaf_of_type _ _).mp H.property
  exact (hs.isSeparated _ (Presheaf.imageSieve_mem _ e b)).ext
    (fun V i hi => h V i hi.choose hi.choose_spec)

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {F : Type v} [Field F] [Algebra O F]
variable {σ τ υ ω : Type} [Finite σ] [Finite τ] [Finite υ] [Finite ω]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}
variable {P : ModuleLaw O R υ} {Q : ModuleLaw O R ω}

namespace RationalSection

/-- Composition is additive in its right argument on all actual sheaf sections. -/
@[simp]
theorem comp_add {U : Opens (PrimeSpectrum R)}
    (g : RationalSection F N P U) (f₁ f₂ : RationalSection F M N U) :
    comp g (f₁ + f₂) = comp g f₁ + comp g f₂ := by
  apply eq_of_local_lifts
    (SheafifyPairing.pairsMap (rationalHomTypeUnit F N P)
      (SheafifyPairing.pairsMap (rationalHomTypeUnit F M N) (rationalHomTypeUnit F M N)))
    (rationalHomTypeSheaf F M P) (g, (f₁, f₂))
  rintro V i ⟨g', f₁', f₂'⟩ heq
  change (ofRational V g', (ofRational V f₁', ofRational V f₂')) =
    (restrict i g, (restrict i f₁, restrict i f₂)) at heq
  obtain ⟨hg, hf⟩ := Prod.mk.inj heq
  obtain ⟨hf₁, hf₂⟩ := Prod.mk.inj hf
  change restrict i (comp g (f₁ + f₂)) = restrict i (comp g f₁ + comp g f₂)
  simp only [restrict_comp_hom, map_add, ← hg, ← hf₁, ← hf₂]
  erw [← map_add, comp_ofRational, RationalHom.comp_add, map_add,
    comp_ofRational, comp_ofRational]

/-- Composition is additive in its left argument on all actual sheaf sections. -/
@[simp]
theorem add_comp {U : Opens (PrimeSpectrum R)}
    (g₁ g₂ : RationalSection F N P U) (f : RationalSection F M N U) :
    comp (g₁ + g₂) f = comp g₁ f + comp g₂ f := by
  apply eq_of_local_lifts
    (SheafifyPairing.pairsMap (rationalHomTypeUnit F N P)
      (SheafifyPairing.pairsMap (rationalHomTypeUnit F N P) (rationalHomTypeUnit F M N)))
    (rationalHomTypeSheaf F M P) (g₁, (g₂, f))
  rintro V i ⟨g₁', g₂', f'⟩ heq
  change (ofRational V g₁', (ofRational V g₂', ofRational V f')) =
    (restrict i g₁, (restrict i g₂, restrict i f)) at heq
  obtain ⟨hg₁, hgf⟩ := Prod.mk.inj heq
  obtain ⟨hg₂, hf⟩ := Prod.mk.inj hgf
  change restrict i (comp (g₁ + g₂) f) = restrict i (comp g₁ f + comp g₂ f)
  simp only [restrict_comp_hom, map_add, ← hg₁, ← hg₂, ← hf]
  erw [← map_add, comp_ofRational, RationalHom.add_comp, map_add,
    comp_ofRational, comp_ofRational]

/-- Composition is F-linear in its right argument on actual sections. -/
@[simp]
theorem comp_smul {U : Opens (PrimeSpectrum R)}
    (g : RationalSection F N P U) (a : F) (f : RationalSection F M N U) :
    comp g (a • f) = a • comp g f := by
  apply eq_of_local_lifts
    (SheafifyPairing.pairsMap (rationalHomTypeUnit F N P) (rationalHomTypeUnit F M N))
    (rationalHomTypeSheaf F M P) (g, f)
  rintro V i ⟨g', f'⟩ heq
  change (ofRational V g', ofRational V f') = (restrict i g, restrict i f) at heq
  obtain ⟨hg, hf⟩ := Prod.mk.inj heq
  change restrict i (comp g (a • f)) = restrict i (a • comp g f)
  simp only [restrict_comp_hom, map_smul, ← hg, ← hf]
  erw [← map_smul, comp_ofRational, RationalHom.comp_smul, map_smul, comp_ofRational]

/-- Composition is F-linear in its left argument on actual sections. -/
@[simp]
theorem smul_comp {U : Opens (PrimeSpectrum R)}
    (a : F) (g : RationalSection F N P U) (f : RationalSection F M N U) :
    comp (a • g) f = a • comp g f := by
  apply eq_of_local_lifts
    (SheafifyPairing.pairsMap (rationalHomTypeUnit F N P) (rationalHomTypeUnit F M N))
    (rationalHomTypeSheaf F M P) (g, f)
  rintro V i ⟨g', f'⟩ heq
  change (ofRational V g', ofRational V f') = (restrict i g, restrict i f) at heq
  obtain ⟨hg, hf⟩ := Prod.mk.inj heq
  change restrict i (comp (a • g) f) = restrict i (a • comp g f)
  simp only [restrict_comp_hom, map_smul, ← hg, ← hf]
  erw [← map_smul, comp_ofRational, RationalHom.smul_comp, map_smul, comp_ofRational]

/-- The actual composition operation as an F-bilinear map. -/
def compLinear {U : Opens (PrimeSpectrum R)} :
    RationalSection F N P U →ₗ[F] RationalSection F M N U →ₗ[F] RationalSection F M P U where
  toFun g := {
    toFun := comp g
    map_add' := comp_add g
    map_smul' := comp_smul g }
  map_add' g₁ g₂ := by
    apply LinearMap.ext
    intro f
    exact add_comp g₁ g₂ f
  map_smul' a g := by
    apply LinearMap.ext
    intro f
    exact smul_comp a g f

@[simp]
theorem comp_zero {U : Opens (PrimeSpectrum R)} (g : RationalSection F N P U) :
    comp g (0 : RationalSection F M N U) = 0 :=
  (compLinear g).map_zero

@[simp]
theorem zero_comp {U : Opens (PrimeSpectrum R)} (f : RationalSection F M N U) :
    comp (0 : RationalSection F N P U) f = 0 :=
  compLinear.map_zero₂ f

/-- The identity section is the image of the actual tensor identity on each open. -/
def id (M : ModuleLaw O R σ) (U : Opens (PrimeSpectrum R)) : RationalSection F M M U :=
  ofRational U (RationalHom.id (F := F)
    (M.overAlgebra ((coefficientStructurePresheaf R).obj (op U))))

@[simp]
theorem restrict_id_section {U V : Opens (PrimeSpectrum R)} (i : V ⟶ U) :
    restrict i (id (F := F) M U) = id M V := by
  erw [id, restrict_ofRational]
  change ofRational V
    (RationalHom.algebraMapLinear ((coefficientStructurePresheaf R).map i.op)
      (RationalHom.id (M.overAlgebra ((coefficientStructurePresheaf R).obj (op U))))) = _
  erw [RationalHom.algebraMapLinear_hom_id]
  rfl

@[simp]
theorem comp_id {U : Opens (PrimeSpectrum R)} (f : RationalSection F M N U) :
    comp f (id M U) = f := by
  apply eq_of_local_lifts (rationalHomTypeUnit F M N)
    (rationalHomTypeSheaf F M N) f
  intro V i f' hf
  change ofRational V f' = restrict i f at hf
  change restrict i (comp f (id M U)) = restrict i f
  rw [restrict_comp_hom, restrict_id_section, ← hf, id]
  erw [comp_ofRational, RationalHom.comp_id]

@[simp]
theorem id_comp {U : Opens (PrimeSpectrum R)} (f : RationalSection F M N U) :
    comp (id N U) f = f := by
  apply eq_of_local_lifts (rationalHomTypeUnit F M N)
    (rationalHomTypeSheaf F M N) f
  intro V i f' hf
  change ofRational V f' = restrict i f at hf
  change restrict i (comp (id N U) f) = restrict i f
  rw [restrict_comp_hom, restrict_id_section, ← hf, id]
  erw [comp_ofRational, RationalHom.id_comp]

/-- Composition of arbitrary rational sections is associative. -/
theorem comp_assoc {U : Opens (PrimeSpectrum R)}
    (h : RationalSection F P Q U) (g : RationalSection F N P U)
    (f : RationalSection F M N U) : comp (comp h g) f = comp h (comp g f) := by
  apply eq_of_local_lifts
    (SheafifyPairing.pairsMap (rationalHomTypeUnit F P Q)
      (SheafifyPairing.pairsMap (rationalHomTypeUnit F N P) (rationalHomTypeUnit F M N)))
    (rationalHomTypeSheaf F M Q) (h, (g, f))
  rintro V i ⟨h', g', f'⟩ heq
  change (ofRational V h', (ofRational V g', ofRational V f')) =
    (restrict i h, (restrict i g, restrict i f)) at heq
  obtain ⟨hh, hgf⟩ := Prod.mk.inj heq
  obtain ⟨hg, hf⟩ := Prod.mk.inj hgf
  change restrict i (comp (comp h g) f) = restrict i (comp h (comp g f))
  simp only [restrict_comp_hom, ← hh, ← hg, ← hf, comp_ofRational]
  erw [comp_ofRational, comp_ofRational, RationalHom.comp_assoc]

end RationalSection
end Langlands.FormalGroup.ModuleLaw
