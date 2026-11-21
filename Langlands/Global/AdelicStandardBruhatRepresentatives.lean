import Langlands.Global.AdelicLeadingCuspidalComponents
import Langlands.Global.AdelicEisensteinDoubleCosetsProof

/-! # Rational representatives indexed by minimal Weyl elements -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme AdelicGroupPoints Langlands.Automorphic.GroupSchemeFunctions
  Langlands.Aubert.General.RationalPointFamily Langlands.Group.RelativeWeylIndexing
  Langlands.GroupScheme.GaloisPointComparison

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)
  {CM : CoxeterMatrix (SimpleRoot fam.i fam.ν)}
  (cs : CoxeterSystem CM (relativeWeylGroup fam.i))
  (P Q : Finset (SimpleRoot fam.i fam.ν))
  (I J : StandardIndex F G fam.i fam.ν)

local notation "Index" => {w : relativeWeylGroup fam.i // IsMinimal cs Q P w}
local notation "liftWeyl" => fun x : normalizerPoints fam.i => (QuotientGroup.mk x : relativeWeylGroup fam.i)

/-- Any rational lifts of the minimal Weyl elements give actual double
coset representatives for the supplied standard parabolics. -/
def StandardBruhatRepresentativesStatement : Prop :=
  IsRelativeWeylCoxeterRealization fam.i fam.ν cs →
  rootSet fam.i fam.ν P = I.val → rootSet fam.i fam.ν Q = J.val →
  ∀ lift : Index → normalizerPoints fam.i, (∀ w, liftWeyl (lift w) = w.val) →
    IsDoubleCosetRepresentatives F (fam.p J) (fam.p I) (fun w => (lift w).val)

set_option maxHeartbeats 1800000 in
theorem standardBruhatRepresentatives : StandardBruhatRepresentativesStatement fam cs P Q I J := by
  intro hcs hI hJ n hn
  classical
  obtain ⟨e, he⟩ := (standardParabolicPointsStatement_proof F G fam.connectedReductive
    fam.T fam.i fam.maximalSplit fam.ν fam.generic).2.2.2
    (rootSet fam.i fam.ν Q) (rootSet fam.i fam.ν P)
    (rootSet_subset fam.i fam.ν Q) (rootSet_subset fam.i fam.ν P)
  let WP := standardRelativeWeylGroup fam.i fam.ν (rootSet fam.i fam.ν P)
  let WQ := standardRelativeWeylGroup fam.i fam.ν (rootSet fam.i fam.ν Q)
  let PP := standardParabolicPoints fam.i fam.ν (rootSet fam.i fam.ν P)
  let PQ := standardParabolicPoints fam.i fam.ν (rootSet fam.i fam.ν Q)
  have he' (w : Index) : e (DoubleCoset.mk WQ WP w.val) = DoubleCoset.mk PQ PP (n w).val := by
    rw [← hn]
    exact he (n w)
  have hclass (w v : relativeWeylGroup fam.i) :
      DoubleCoset.mk WQ WP w = DoubleCoset.mk WQ WP v ↔ v ∈ doubleCoset cs Q P w := by
    rw [DoubleCoset.eq]
    change (∃ a ∈ WQ, ∃ b ∈ WP, v = a * w * b) ↔ _
    rw [show WQ = standardSubgroup cs Q from (hcs.2.2.2.2 Q).symm,
      show WP = standardSubgroup cs P from (hcs.2.2.2.2 P).symm]
    rfl
  have hI' : rationalImage F (fam.p I) = PP.map (principalPoint F G) := by
    rw [rationalImage_eq_map_range, (fam.isCompatible I).parabolic_eq, ← hI]
  have hJ' : rationalImage F (fam.p J) = PQ.map (principalPoint F G) := by
    rw [rationalImage_eq_map_range, (fam.isCompatible J).parabolic_eq, ← hJ]
  intro z hz
  obtain ⟨q, rfl⟩ := hz
  obtain ⟨y, rfl⟩ := (rationalCoeffEquiv F G).surjective q
  have hrep (w : Index) :
      (∃ x ∈ rationalImage F (fam.p J), ∃ t ∈ rationalImage F (fam.p I),
        principalPoint F G y = x * innerAdelicPoint F G (n w).val * t) ↔
      DoubleCoset.mk PQ PP (n w).val = DoubleCoset.mk PQ PP y := by
    rw [DoubleCoset.eq, hI', hJ', ← principalPoint_eq_innerAdelicPoint]
    have hinj : Function.Injective (principalPoint F G) :=
      (rational_injective F G).comp (rationalCoeffEquiv F G).injective
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨t, ht, rfl⟩, hz⟩
      exact ⟨x, hx, t, ht, hinj (by simpa only [map_mul] using hz)⟩
    · rintro ⟨x, hx, t, ht, rfl⟩
      exact ⟨_, ⟨x, hx, rfl⟩, _, ⟨t, ht, rfl⟩, by simp only [map_mul]⟩
  let w₀ := (e.symm (DoubleCoset.mk PQ PP y)).out
  have hw₀ : e (DoubleCoset.mk WQ WP w₀) = DoubleCoset.mk PQ PP y := by
    rw [DoubleCoset.out_eq', e.apply_symm_apply]
  obtain ⟨v, hv, hvmin⟩ := exists_minimal_in_doubleCoset_unrestricted cs Q P w₀
  let w : Index := ⟨v, hvmin⟩
  refine ⟨w, (hrep w).mpr ?_, ?_⟩
  · rw [← he', ← hw₀]
    exact congrArg e ((hclass w₀ v).mpr hv).symm
  · intro k hk
    apply Subtype.ext
    have hkClass : DoubleCoset.mk WQ WP w₀ = DoubleCoset.mk WQ WP k.val :=
      e.injective (hw₀.trans ((he' k).trans ((hrep k).mp hk)).symm)
    exact minimalRepresentativeUnique_proof cs Q P w₀ k.val v
      ((hclass _ _).mp hkClass) hv k.property hvmin

/-- The lifts can use a prescribed rational normalizer point on the class
it represents whenever that Weyl element is minimal. -/
theorem exists_standardBruhatRepresentatives (n : normalizerPoints fam.i)
    (hcs : IsRelativeWeylCoxeterRealization fam.i fam.ν cs)
    (hI : rootSet fam.i fam.ν P = I.val) (hJ : rootSet fam.i fam.ν Q = J.val) :
    ∃ lift : Index → normalizerPoints fam.i,
      (∀ w, liftWeyl (lift w) = w.val) ∧
      (∀ w, w.val = liftWeyl n → lift w = n) ∧
      IsDoubleCosetRepresentatives F (fam.p J) (fam.p I) (fun w => (lift w).val) := by
  classical
  let lift (w : Index) :=
    if w.val = liftWeyl n then n else (QuotientGroup.mk_surjective w.val).choose
  have hLift (w : Index) : liftWeyl (lift w) = w.val := by
    dsimp only [lift]
    split_ifs with h
    · exact h.symm
    · exact (QuotientGroup.mk_surjective w.val).choose_spec
  exact ⟨lift, hLift, fun w hw => by simp [lift, hw],
    fam.standardBruhatRepresentatives cs P Q I J hcs hI hJ lift hLift⟩

end Langlands.Global.StandardParabolicFamily
