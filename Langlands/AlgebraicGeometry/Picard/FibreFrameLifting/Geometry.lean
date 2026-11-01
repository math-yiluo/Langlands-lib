import Langlands.AlgebraicGeometry.Picard.FibreFrameLifting.Squares
import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Base-change squares over an affine open, its fibre and a smaller affine open

For morphisms `h : X ⟶ S` and `h₁ : X₁ ⟶ S` with `i : X₁ ⟶ X` over `S`, these are the pullback
squares relating the base changes of `X₁ ⟶ X` along the inclusion of an affine open
`Spec R ⟶ S`, along a point `Spec κ ⟶ S` factoring through it, and along a smaller affine
open of `S`.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard.FibreFrameLifting

variable {S X X₁ : Scheme.{u}} (h : X ⟶ S) (h₁ : X₁ ⟶ S) (i : X₁ ⟶ X) (hi : i ≫ h = h₁)

/-- The base change of `i : X₁ ⟶ X` (over `S`) along `t : T ⟶ S`. -/
def mapOver {T : Scheme.{u}} (t : T ⟶ S) : pullback h₁ t ⟶ pullback h t :=
  pullback.lift (pullback.fst h₁ t ≫ i) (pullback.snd h₁ t)
    (by rw [Category.assoc, hi, pullback.condition])

@[reassoc (attr := simp)]
lemma mapOver_fst {T : Scheme.{u}} (t : T ⟶ S) :
    mapOver h h₁ i hi t ≫ pullback.fst h t = pullback.fst h₁ t ≫ i :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma mapOver_snd {T : Scheme.{u}} (t : T ⟶ S) :
    mapOver h h₁ i hi t ≫ pullback.snd h t = pullback.snd h₁ t :=
  pullback.lift_snd _ _ _

/-- The base change of `i` is a pullback of `i`. -/
theorem isPullback_mapOver {T : Scheme.{u}} (t : T ⟶ S) :
    IsPullback (pullback.fst h₁ t) (mapOver h h₁ i hi t) i (pullback.fst h t) :=
  isPullback_of_over (IsPullback.of_hasPullback h₁ t) (IsPullback.of_hasPullback h t) hi
    (mapOver_fst h h₁ i hi t) (mapOver_snd h h₁ i hi t)

variable {R κ : CommRingCat.{u}} (e : Spec R ⟶ S) (φ₀ : R ⟶ κ) (t : Spec κ ⟶ S)
  (ht : t = Spec.map φ₀ ≫ e)

/-- The comparison from the base change along `t = Spec φ₀ ≫ e` to the base change along `e`. -/
def liftPoint : pullback h t ⟶ pullback h e :=
  pullback.lift (pullback.fst h t) (pullback.snd h t ≫ Spec.map φ₀)
    (by rw [pullback.condition, ht, Category.assoc])

@[reassoc (attr := simp)]
lemma liftPoint_fst : liftPoint h e φ₀ t ht ≫ pullback.fst h e = pullback.fst h t :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma liftPoint_snd :
    liftPoint h e φ₀ t ht ≫ pullback.snd h e = pullback.snd h t ≫ Spec.map φ₀ :=
  pullback.lift_snd _ _ _

/-- The base change along `t` is the base change of the base change along `e`. -/
theorem isPullback_liftPoint :
    IsPullback (liftPoint h e φ₀ t ht) (pullback.snd h t) (pullback.snd h e) (Spec.map φ₀) := by
  refine IsPullback.of_right ?_ (liftPoint_snd h e φ₀ t ht) (IsPullback.of_hasPullback h e)
  rw [liftPoint_fst]
  subst ht
  exact IsPullback.of_hasPullback h _

/-- The base change of `i` along `t` is the base change along `Spec φ₀` of its base change
along `e`. -/
theorem isPullback_liftPoint_mapOver :
    IsPullback (liftPoint h₁ e φ₀ t ht) (mapOver h h₁ i hi t) (mapOver h h₁ i hi e)
      (liftPoint h e φ₀ t ht) := by
  refine IsPullback.of_right ?_ ?_ (isPullback_mapOver h h₁ i hi e)
  · rw [liftPoint_fst, liftPoint_fst]
    exact isPullback_mapOver h h₁ i hi t
  · apply pullback.hom_ext
    · simp only [Category.assoc, mapOver_fst, liftPoint_fst, liftPoint_fst_assoc, mapOver_fst]
    · simp only [Category.assoc, mapOver_snd, liftPoint_snd, liftPoint_snd, mapOver_snd_assoc]

section AffineOpen

variable {V U : S.Opens} (hV : IsAffineOpen V) (hU : IsAffineOpen U) (hUV : U ≤ V)

/-- For affine opens `U ≤ V`, the comparison from the base change along `U.ι` to the base change
along `hV.fromSpec`, lying over `Spec` of the restriction `Γ(S, V) ⟶ Γ(S, U)`. -/
def liftAffineOpen : pullback h U.ι ⟶ pullback h hV.fromSpec :=
  pullback.lift (pullback.fst h U.ι)
    ((pullback.snd h U.ι ≫ hU.isoSpec.hom) ≫ Spec.map (S.presheaf.map (homOfLE hUV).op))
    (by rw [pullback.condition, Category.assoc, Category.assoc,
      hV.map_fromSpec hU (homOfLE hUV).op, hU.isoSpec_hom_fromSpec])

@[reassoc (attr := simp)]
lemma liftAffineOpen_fst :
    liftAffineOpen h hV hU hUV ≫ pullback.fst h hV.fromSpec = pullback.fst h U.ι :=
  pullback.lift_fst _ _ _

/-- Over affine opens `U ≤ V`, the base change along `U.ι`, mapped to `Spec Γ(S, U)` by
`hU.isoSpec`, is the base change along the restriction `Γ(S, V) ⟶ Γ(S, U)` of the base change
along `hV.fromSpec`. -/
theorem isPullback_liftAffineOpen :
    IsPullback (liftAffineOpen h hV hU hUV) (pullback.snd h U.ι ≫ hU.isoSpec.hom)
      (pullback.snd h hV.fromSpec) (Spec.map (S.presheaf.map (homOfLE hUV).op)) := by
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback h _)
  rw [liftAffineOpen_fst]
  refine (IsPullback.of_hasPullback h U.ι).of_iso (Iso.refl _) (Iso.refl _) hU.isoSpec
    (Iso.refl _) (by simp) (by simp) (by simp) ?_
  rw [Iso.refl_hom, Category.comp_id, hV.map_fromSpec hU (homOfLE hUV).op,
    hU.isoSpec_hom_fromSpec]

end AffineOpen

/-- The fibre of `X ×_S U ⟶ U` over a point of an open `U` lies over the fibre of `X ⟶ S`
over the same point. -/
theorem fiberι_fst_comp_eq {U : S.Opens} (x : U) :
    ((pullback.snd h U.ι).fiberι x ≫ pullback.fst h U.ι) ≫ h =
      ((pullback.snd h U.ι).fiberToSpecResidueField x ≫ Spec.map (U.ι.residueFieldMap x)) ≫
        S.fromSpecResidueField (U.ι x) := by
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  refine (congrArg (· ≫ U.ι) ((pullback.snd h U.ι).fiber_fac x)).trans ?_
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
    (U.ι.SpecMap_residueFieldMap_fromSpecResidueField x).symm).trans (Category.assoc _ _ _).symm)

end Langlands.AlgebraicGeometry.Picard.FibreFrameLifting
