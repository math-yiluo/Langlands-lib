import Langlands.GroupScheme.Torus.HenselianNormalizerLifting
import Langlands.GroupScheme.Torus.SplitLatticeBaseChange
import Langlands.GroupScheme.Rational.NormalizerGaloisAction

/-! # Henselian normalizer lifts that negate an actual character -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

section CharacterTransport

variable {S S' : Scheme.{u}} (b : S' ⟶ S)
    {T : CommGroupScheme S} (σ : T ≅ T)

/-- Negation of a character is preserved by every base change. -/
theorem characterAut_baseChange_eq_neg {a : characterLattice T}
    (hσ : characterAut σ a = -a) :
    characterAut ((CommGroupScheme.baseChange b).mapIso σ)
      (characterLattice.baseChange b T a) =
        -characterLattice.baseChange b T a := by
  rw [characterAut_baseChange, hσ, map_neg]

end CharacterTransport

section SplitCharacters

variable {R k : Type u} [CommRing R] [IsDomain R] [Field k]
    (b : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    {T : CommGroupScheme (Spec (CommRingCat.of R))}

/-- Over a domain, negation detected on a field fibre of a split torus is
already negation of the original integral character. -/
theorem IsSplitTorus.characterAut_eq_neg_of_baseChange
    (hT : IsSplitTorus T.toGrp) (σ : T ≅ T) (a : characterLattice T)
    (hσ : characterAut ((CommGroupScheme.baseChange b).mapIso σ)
      (characterLattice.baseChange b T a) =
        -characterLattice.baseChange b T a) :
    characterAut σ a = -a := by
  apply (hT.characterLattice_baseChange_bijective b T).injective
  rw [← characterAut_baseChange, map_neg]
  exact hσ

end SplitCharacters

section HenselianLifting

variable {R k : Type u} [CommRing R] [IsDomain R] [HenselianLocalRing R]
    [Field k] [Algebra R k]
    {T : CommGroupScheme (Spec (CommRingCat.of R))}
    {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffine G.X.left]
    (i : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp)
    (hG : Smooth G.X.hom) (hk : Function.Surjective (algebraMap R k))
    (a : characterLattice T)

include hT hG hk in
/-- A specified residue normalizer negating the residue of an integral
character lifts to an integral normalizer negating that same character.
Both the residue point and its prescribed automorphism are recovered. -/
theorem exists_henselian_rootNormalizer
    (n₀ : rationalPoints ((baseChange (Spec.algebraMap R k)).obj G))
    (σ₀ : (CommGroupScheme.baseChange (Spec.algebraMap R k)).obj T ≅
      (CommGroupScheme.baseChange (Spec.algebraMap R k)).obj T)
    (hn₀ : IsNormalizingPoint ((baseChange (Spec.algebraMap R k)).map i) n₀ σ₀)
    (hσ₀ : characterAut σ₀ (characterLattice.baseChange (Spec.algebraMap R k) T a) =
      -characterLattice.baseChange (Spec.algebraMap R k) T a) :
    ∃ (n : rationalPoints G) (σ : T ≅ T),
      IsNormalizingPoint i n σ ∧
        baseChangeSectionHom (Spec.algebraMap R k) G n = n₀ ∧
        (CommGroupScheme.baseChange (Spec.algebraMap R k)).mapIso σ = σ₀ ∧
        characterAut σ a = -a := by
  obtain ⟨n, σ, hn, hrec, hσ⟩ :=
    exists_henselian_normalizer i hT hG hk n₀ σ₀ hn₀
  refine ⟨n, σ, hn, hrec, hσ, ?_⟩
  apply hT.characterAut_eq_neg_of_baseChange (Spec.algebraMap R k) σ a
  rwa [hσ]

/-- An actual integral lift of the prescribed character-negating residue
normalizer, retaining the exact point, automorphism and integral action. -/
def henselianRootNormalizerLift
    (n₀ : rationalPoints ((baseChange (Spec.algebraMap R k)).obj G))
    (σ₀ : (CommGroupScheme.baseChange (Spec.algebraMap R k)).obj T ≅
      (CommGroupScheme.baseChange (Spec.algebraMap R k)).obj T)
    (hn₀ : IsNormalizingPoint ((baseChange (Spec.algebraMap R k)).map i) n₀ σ₀)
    (hσ₀ : characterAut σ₀ (characterLattice.baseChange (Spec.algebraMap R k) T a) =
      -characterLattice.baseChange (Spec.algebraMap R k) T a) :
    {p : rationalPoints G × (T ≅ T) //
      IsNormalizingPoint i p.1 p.2 ∧
        baseChangeSectionHom (Spec.algebraMap R k) G p.1 = n₀ ∧
        (CommGroupScheme.baseChange (Spec.algebraMap R k)).mapIso p.2 = σ₀ ∧
        characterAut p.2 a = -a} :=
  Classical.indefiniteDescription _ (by
    obtain ⟨n, σ, hn⟩ := exists_henselian_rootNormalizer i hT hG hk a n₀ σ₀ hn₀ hσ₀
    exact ⟨(n, σ), hn⟩)

end HenselianLifting

section GenericAction

variable {R K : Type u} [CommRing R] [Field K] [Algebra R K]
    {T : CommGroupScheme (Spec (CommRingCat.of R))}
    {G : GroupScheme (Spec (CommRingCat.of R))}
    (i : T.toGrp ⟶ G) (n : rationalPoints G) (σ : T ≅ T)

/-- The same integral normalizing equation gives the actual generic
normalizer, and its character action negates the actual generic character. -/
theorem rootNormalizer_fieldBaseChange (a : characterLattice T)
    (hn : IsNormalizingPoint i n σ) (hσ : characterAut σ a = -a) :
    IsNormalizingPoint ((baseChange (Spec.algebraMap R K)).map i)
        (baseChangeSectionHom (Spec.algebraMap R K) G n)
        ((CommGroupScheme.baseChange (Spec.algebraMap R K)).mapIso σ) ∧
      characterAut ((CommGroupScheme.baseChange (Spec.algebraMap R K)).mapIso σ)
        (characterLattice.baseChange (Spec.algebraMap R K) T a) =
          -characterLattice.baseChange (Spec.algebraMap R K) T a :=
  ⟨hn.baseChangeBasePoint (Spec.algebraMap R K),
    characterAut_baseChange_eq_neg (Spec.algebraMap R K) σ hσ⟩

end GenericAction

end Langlands.GroupScheme
