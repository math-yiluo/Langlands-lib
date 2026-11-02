import Langlands.GroupScheme.SubgroupFunctor
import Langlands.GroupScheme.Multiplicative
import Mathlib.AlgebraicGeometry.AffineSpace

/-! # Dynamic subgroup functors attached to a cocharacter

For a cocharacter `χ : 𝔾_{m,S} ⟶ G` of a group scheme over an arbitrary base scheme `S`, this
module defines the conjugation orbit map of a point, its extensions from `T ×_S 𝔾_{m,S}` to
`T ×_S 𝔸¹_S`, their values at the zero section, and the dynamic subgroup functors `P_G(χ)`,
`Z_G(χ)` and `U_G(χ)` on all schemes over `S`.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}}

namespace AffineLine

/-- The affine line `𝔸¹_S` over `S`: Mathlib's affine space `𝔸(PUnit; S)` with its structure
morphism. -/
def scheme (S : Scheme.{u}) : Over S :=
  Over.mk (𝔸(PUnit.{u + 1}; S) ↘ S)

/-- The standard coordinate function on the affine line. -/
def coord (S : Scheme.{u}) : Γ((scheme S).left, ⊤) :=
  AffineSpace.coord S PUnit.unit

/-- Morphisms over `S` from `T` to the affine line are the global functions on `T`. -/
def homEquiv (T : Over S) : (T ⟶ scheme S) ≃ Γ(T.left, ⊤) where
  toFun x := x.left.appTop (coord S)
  invFun f := Over.homMk (AffineSpace.homOfVector T.hom fun _ => f)
    (AffineSpace.homOfVector_over _ _)
  left_inv x := by
    apply Over.OverMorphism.ext
    apply AffineSpace.hom_ext
    · exact (AffineSpace.homOfVector_over T.hom _).trans (Over.w x).symm
    · intro i
      exact AffineSpace.homOfVector_appTop_coord T.hom _ i
  right_inv f := AffineSpace.homOfVector_appTop_coord _ _ _

theorem homEquiv_apply (T : Over S) (x : T ⟶ scheme S) :
    homEquiv T x = x.left.appTop (coord S) :=
  rfl

/-- The function attached to a restricted morphism is the pullback of the function. -/
theorem homEquiv_comp {T T' : Over S} (a : T' ⟶ T) (x : T ⟶ scheme S) :
    homEquiv T' (a ≫ x) = a.left.appTop (homEquiv T x) := by
  rw [homEquiv_apply, homEquiv_apply, Over.comp_left, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply]

/-- Morphisms to the affine line agree when their functions agree. -/
theorem hom_ext {T : Over S} {x y : T ⟶ scheme S} (h : homEquiv T x = homEquiv T y) : x = y :=
  (homEquiv T).injective h

/-- The standard inclusion `𝔾_{m,S} ⟶ 𝔸¹_S`, sending a unit to its underlying function. -/
def unitInclusion (S : Scheme.{u}) : (Gm S).X ⟶ scheme S :=
  (homEquiv (Gm S).X).symm (Gm.pointsEquiv S (Gm S).X (𝟙 _) : Γ((Gm S).X.left, ⊤))

/-- On points, the inclusion of `𝔾_m` in `𝔸¹` forgets that a function is a unit. -/
theorem homEquiv_comp_unitInclusion {T : Over S} (x : T ⟶ (Gm S).X) :
    homEquiv T (x ≫ unitInclusion S) = (Gm.pointsEquiv S T x : Γ(T.left, ⊤)) := by
  rw [homEquiv_comp, unitInclusion, Equiv.apply_symm_apply]
  have h := Gm.pointsEquiv_naturality S x (𝟙 (Gm S).X)
  rw [Category.comp_id] at h
  rw [h]
  rfl

/-- The zero section `S ⟶ 𝔸¹_S`. -/
def zeroSection (S : Scheme.{u}) : 𝟙_ (Over S) ⟶ scheme S :=
  (homEquiv (𝟙_ (Over S))).symm 0

/-- Every point factoring through the zero section is the zero function. -/
theorem homEquiv_comp_zeroSection {T : Over S} (x : T ⟶ 𝟙_ (Over S)) :
    homEquiv T (x ≫ zeroSection S) = 0 := by
  rw [homEquiv_comp, zeroSection, Equiv.apply_symm_apply, map_zero]

end AffineLine

namespace Dynamic

variable {G : GroupScheme S} (χ : (Gm S).toGrp ⟶ G)

/-- The conjugation orbit map `t ↦ χ(t) g χ(t)⁻¹` of a point `g : T ⟶ G`, as the morphism
`T ×_S 𝔾_{m,S} ⟶ G` given by the group law on points of `T ×_S 𝔾_{m,S}`. -/
def orbit {T : Over S} (g : T ⟶ G.X) : T ⊗ (Gm S).X ⟶ G.X :=
  (snd T (Gm S).X ≫ χ.hom.hom) * (fst T (Gm S).X ≫ g) * (snd T (Gm S).X ≫ χ.hom.hom)⁻¹

theorem orbit_one {T : Over S} : orbit χ (1 : T ⟶ G.X) = 1 := by
  simp only [orbit, MonObj.comp_one, mul_one, mul_inv_cancel]

theorem orbit_mul {T : Over S} (g h : T ⟶ G.X) : orbit χ (g * h) = orbit χ g * orbit χ h := by
  simp only [orbit, MonObj.comp_mul]
  group

theorem orbit_inv {T : Over S} (g : T ⟶ G.X) : orbit χ g⁻¹ = (orbit χ g)⁻¹ := by
  simp only [orbit, GrpObj.comp_inv]
  group

/-- Orbit maps are natural in the test scheme. -/
theorem whiskerRight_orbit {T T' : Over S} (a : T' ⟶ T) (g : T ⟶ G.X) :
    a ▷ (Gm S).X ≫ orbit χ g = orbit χ (a ≫ g) := by
  simp only [orbit, MonObj.comp_mul, GrpObj.comp_inv, whiskerRight_snd_assoc,
    whiskerRight_fst_assoc]

/-- `e : T ×_S 𝔸¹_S ⟶ G` extends the orbit map of `g` along `T ×_S 𝔾_{m,S} ⊆ T ×_S 𝔸¹_S`. -/
def IsOrbitExtension {T : Over S} (g : T ⟶ G.X) (e : T ⊗ AffineLine.scheme S ⟶ G.X) : Prop :=
  T ◁ AffineLine.unitInclusion S ≫ e = orbit χ g

/-- The value of a morphism on `T ×_S 𝔸¹_S` along the zero section `T ⟶ T ×_S 𝔸¹_S`. -/
def evalZero {T Y : Over S} (e : T ⊗ AffineLine.scheme S ⟶ Y) : T ⟶ Y :=
  lift (𝟙 T) (toUnit T ≫ AffineLine.zeroSection S) ≫ e

theorem evalZero_mul {T : Over S} (e e' : T ⊗ AffineLine.scheme S ⟶ G.X) :
    evalZero (e * e') = evalZero e * evalZero e' :=
  MonObj.comp_mul _ _ _

theorem evalZero_one {T : Over S} : evalZero (1 : T ⊗ AffineLine.scheme S ⟶ G.X) = 1 :=
  MonObj.comp_one _

theorem evalZero_inv {T : Over S} (e : T ⊗ AffineLine.scheme S ⟶ G.X) :
    evalZero e⁻¹ = (evalZero e)⁻¹ :=
  GrpObj.comp_inv _ _

/-- Evaluation at zero is natural in the test scheme. -/
theorem evalZero_whiskerRight {T T' Y : Over S} (a : T' ⟶ T)
    (e : T ⊗ AffineLine.scheme S ⟶ Y) :
    evalZero (a ▷ AffineLine.scheme S ≫ e) = a ≫ evalZero e := by
  simp only [evalZero, ← Category.assoc]
  congr 1
  ext <;> simp

theorem evalZero_fst {T Y : Over S} (g : T ⟶ Y) :
    evalZero (fst T (AffineLine.scheme S) ≫ g) = g := by
  simp [evalZero]

theorem IsOrbitExtension.one {T : Over S} : IsOrbitExtension χ (1 : T ⟶ G.X) 1 := by
  rw [IsOrbitExtension, MonObj.comp_one, orbit_one]

theorem IsOrbitExtension.mul {T : Over S} {g h : T ⟶ G.X} {e e' : T ⊗ AffineLine.scheme S ⟶ G.X}
    (he : IsOrbitExtension χ g e) (he' : IsOrbitExtension χ h e') :
    IsOrbitExtension χ (g * h) (e * e') := by
  rw [IsOrbitExtension, MonObj.comp_mul, he, he', orbit_mul]

theorem IsOrbitExtension.inv {T : Over S} {g : T ⟶ G.X} {e : T ⊗ AffineLine.scheme S ⟶ G.X}
    (he : IsOrbitExtension χ g e) : IsOrbitExtension χ g⁻¹ e⁻¹ := by
  rw [IsOrbitExtension, GrpObj.comp_inv, he, orbit_inv]

/-- Restricting an extension along a morphism of test schemes extends the restricted orbit. -/
theorem IsOrbitExtension.whiskerRight {T T' : Over S} (a : T' ⟶ T) {g : T ⟶ G.X}
    {e : T ⊗ AffineLine.scheme S ⟶ G.X} (he : IsOrbitExtension χ g e) :
    IsOrbitExtension χ (a ≫ g) (a ▷ AffineLine.scheme S ≫ e) := by
  rw [IsOrbitExtension, whisker_exchange_assoc, he, whiskerRight_orbit]

/-- `l` is a limit at zero of the orbit of `g`: the zero value of some orbit extension. -/
def HasLimit {T : Over S} (g l : T ⟶ G.X) : Prop :=
  ∃ e, IsOrbitExtension χ g e ∧ evalZero e = l

/-- The dynamic parabolic subgroup functor `P_G(χ)`: points whose conjugation orbit map extends
from `T ×_S 𝔾_{m,S}` to `T ×_S 𝔸¹_S`. -/
def parabolic : SubgroupFunctor G where
  carrier _ :=
    { carrier := {g | ∃ e, IsOrbitExtension χ g e}
      mul_mem' := fun ⟨e, he⟩ ⟨e', he'⟩ => ⟨e * e', he.mul χ he'⟩
      one_mem' := ⟨1, IsOrbitExtension.one χ⟩
      inv_mem' := fun ⟨e, he⟩ => ⟨e⁻¹, he.inv χ⟩ }
  comp_mem a _ := fun ⟨e, he⟩ => ⟨a ▷ AffineLine.scheme S ≫ e, he.whiskerRight χ a⟩

theorem mem_parabolic {T : Over S} {g : T ⟶ G.X} :
    g ∈ (parabolic χ).carrier T ↔ ∃ e, IsOrbitExtension χ g e :=
  Iff.rfl

/-- The centralizer subgroup functor `Z_G(χ)`: points whose conjugation orbit map is constant. -/
def centralizer : SubgroupFunctor G where
  carrier T :=
    { carrier := {g | orbit χ g = fst T (Gm S).X ≫ g}
      mul_mem' := by
        intro g h (hg : orbit χ g = _) (hh : orbit χ h = _)
        change orbit χ (g * h) = _
        rw [orbit_mul, hg, hh, MonObj.comp_mul]
      one_mem' := by
        change orbit χ 1 = _
        rw [orbit_one, MonObj.comp_one]
      inv_mem' := by
        intro g (hg : orbit χ g = _)
        change orbit χ g⁻¹ = _
        rw [orbit_inv, hg, GrpObj.comp_inv] }
  comp_mem a g (hg : orbit χ g = _) := by
    change orbit χ (a ≫ g) = _
    rw [← whiskerRight_orbit, hg, whiskerRight_fst_assoc]

theorem mem_centralizer {T : Over S} {g : T ⟶ G.X} :
    g ∈ (centralizer χ).carrier T ↔ orbit χ g = fst T (Gm S).X ≫ g :=
  Iff.rfl

/-- The dynamic unipotent subgroup functor `U_G(χ)`: points whose orbit map extends with value
the identity at zero. -/
def unipotent : SubgroupFunctor G where
  carrier T :=
    { carrier := {g | HasLimit χ g 1}
      mul_mem' := fun ⟨e, he, he0⟩ ⟨e', he', he0'⟩ =>
        ⟨e * e', he.mul χ he', by rw [evalZero_mul, he0, he0', mul_one]⟩
      one_mem' := ⟨1, IsOrbitExtension.one χ, evalZero_one⟩
      inv_mem' := fun ⟨e, he, he0⟩ => ⟨e⁻¹, he.inv χ, by rw [evalZero_inv, he0, inv_one]⟩ }
  comp_mem a _ := fun ⟨e, he, he0⟩ =>
    ⟨a ▷ AffineLine.scheme S ≫ e, he.whiskerRight χ a,
      by rw [evalZero_whiskerRight, he0, MonObj.comp_one]⟩

theorem mem_unipotent {T : Over S} {g : T ⟶ G.X} :
    g ∈ (unipotent χ).carrier T ↔ HasLimit χ g 1 :=
  Iff.rfl

/-- The unipotent subgroup functor lies in the parabolic one. -/
theorem unipotent_le_parabolic : unipotent χ ≤ parabolic χ :=
  fun _ _ ⟨e, he, _⟩ => ⟨e, he⟩

/-- A centralizing point extends by the constant map, with itself as limit. -/
theorem hasLimit_of_mem_centralizer {T : Over S} {g : T ⟶ G.X}
    (hg : g ∈ (centralizer χ).carrier T) : HasLimit χ g g :=
  ⟨fst T (AffineLine.scheme S) ≫ g, by
    rw [IsOrbitExtension, whiskerLeft_fst_assoc]
    exact hg.symm, evalZero_fst g⟩

/-- The centralizer subgroup functor lies in the parabolic one. -/
theorem centralizer_le_parabolic : centralizer χ ≤ parabolic χ :=
  fun _ _ hg => ⟨_, (hasLimit_of_mem_centralizer χ hg).choose_spec.1⟩

end Dynamic

end Langlands.GroupScheme
