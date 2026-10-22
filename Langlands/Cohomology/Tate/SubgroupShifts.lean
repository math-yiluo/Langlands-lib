import Langlands.Cohomology.Tate.ShiftDefinitions
import Langlands.Cohomology.Tate.ZeroTransferDefinitions

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Tate

set_option backward.isDefEq.respectTransparency false

variable {R G : Type u} [CommRing R] [Group G] (H : Subgroup G)

/-- The coefficient module indexing the coinduced summands after subgroup restriction. -/
abbrev cosetCoefficients (A : Rep.{u} R G) : Rep.{u} R H :=
  Rep.trivial R H ((G ⧸ H) → A)

/-- Functions on the group are functions on the subgroup with coset-indexed coefficients. -/
def restrictedCoinducedCoordinates (A : Rep.{u} R G) :
    Rep.res H.subtype (coinduced A) ≃ₗ[R] coinduced (cosetCoefficients H A) where
  toFun f := coinducedFunctions (cosetCoefficients H A)
    (fun h q => f.1 (cosetDecomposition H (q, h)))
  invFun f := coinducedFunctions A
    (fun g => f.1 ((cosetDecomposition H).symm g).2 ((cosetDecomposition H).symm g).1)
  left_inv f := by
    apply Subtype.ext
    funext g
    change f.1 (cosetDecomposition H ((cosetDecomposition H).symm g)) = f.1 g
    rw [Equiv.apply_symm_apply]
  right_inv f := by
    apply Subtype.ext
    funext h q
    change f.1 ((cosetDecomposition H).symm (cosetDecomposition H (q, h))).2
      ((cosetDecomposition H).symm (cosetDecomposition H (q, h))).1 = f.1 h q
    rw [Equiv.symm_apply_apply]
  map_add' f g := rfl
  map_smul' r f := rfl

/-- Restriction of the actual coinduced replacement remains coinduced from the trivial subgroup. -/
def restrictedCoinducedIso (A : Rep.{u} R G) :
    Rep.res H.subtype (coinduced A) ≅ coinduced (cosetCoefficients H A) :=
  Rep.mkIso (Representation.Equiv.mk (restrictedCoinducedCoordinates H A) (fun g => by
    ext f h q
    change f.1 ((q.out * (h : G)) * (g : G)) = f.1 (q.out * ((h * g : H) : G))
    simp only [Subgroup.coe_mul, mul_assoc]))

variable [Fintype G] [Fintype H]

omit [Fintype G] in
lemma restrictedCoinduced_tate_isZero (A : Rep.{u} R G) (n : ℤ) :
    IsZero (tateCohomology (Rep.res H.subtype (coinduced A)) n) :=
  (coinduced_tate_isZero (cosetCoefficients H A) n).of_iso
    ((tateCohomologyFunctor n).mapIso (restrictedCoinducedIso H A))

omit [Fintype G] [Fintype H] in
lemma restrictedShiftUpSequence_shortExact (A : Rep.{u} R G) :
    ((shiftUpSequence A).map (Rep.resFunctor H.subtype)).ShortExact :=
  (shiftUpSequence_shortExact A).map_of_exact (Rep.resFunctor H.subtype)

omit [Fintype H] in
lemma restrictedShiftDownSequence_shortExact (A : Rep.{u} R G) :
    ((shiftDownSequence A).map (Rep.resFunctor H.subtype)).ShortExact :=
  (shiftDownSequence_shortExact A).map_of_exact (Rep.resFunctor H.subtype)

/-- The same embedding sequence gives the actual Tate shift isomorphism for each subgroup. -/
def restrictedShiftUpIso (A : Rep.{u} R G) (n : ℤ) :
    tateCohomology (Rep.res H.subtype (shiftUp A)) n ≅
      tateCohomology (Rep.res H.subtype A) (n + 1) := by
  have := tate_delta_isIso (restrictedShiftUpSequence_shortExact H A) n
    (restrictedCoinduced_tate_isZero H A n) (restrictedCoinduced_tate_isZero H A (n + 1))
  exact asIso (TateCohomology.δ (restrictedShiftUpSequence_shortExact H A) n)

/-- The same augmentation sequence gives the actual Tate shift isomorphism for each subgroup. -/
def restrictedShiftDownIso (A : Rep.{u} R G) (n : ℤ) :
    tateCohomology (Rep.res H.subtype A) n ≅
      tateCohomology (Rep.res H.subtype (shiftDown A)) (n + 1) := by
  have := tate_delta_isIso (restrictedShiftDownSequence_shortExact H A) n
    (restrictedCoinduced_tate_isZero H A n) (restrictedCoinduced_tate_isZero H A (n + 1))
  exact asIso (TateCohomology.δ (restrictedShiftDownSequence_shortExact H A) n)

omit [Fintype G] in
lemma restrictedShiftUpIso_naturality {A B : Rep.{u} R G} (f : A ⟶ B) (n : ℤ) :
    (restrictedShiftUpIso H A n).hom ≫
        (tateCohomologyFunctor (n + 1)).map ((Rep.resFunctor H.subtype).map f) =
      (tateCohomologyFunctor n).map ((Rep.resFunctor H.subtype).map (shiftUpMap f)) ≫
        (restrictedShiftUpIso H B n).hom :=
  TateCohomology.δ_naturality (restrictedShiftUpSequence_shortExact H A)
    (restrictedShiftUpSequence_shortExact H B)
    ((Rep.resFunctor H.subtype).mapShortComplex.map (shiftUpSequenceMap f)) n

lemma restrictedShiftDownIso_naturality {A B : Rep.{u} R G} (f : A ⟶ B) (n : ℤ) :
    (restrictedShiftDownIso H A n).hom ≫
        (tateCohomologyFunctor (n + 1)).map ((Rep.resFunctor H.subtype).map (shiftDownMap f)) =
      (tateCohomologyFunctor n).map ((Rep.resFunctor H.subtype).map f) ≫
        (restrictedShiftDownIso H B n).hom :=
  TateCohomology.δ_naturality (restrictedShiftDownSequence_shortExact H A)
    (restrictedShiftDownSequence_shortExact H B)
    ((Rep.resFunctor H.subtype).mapShortComplex.map (shiftDownSequenceMap f)) n

end Langlands.Tate
