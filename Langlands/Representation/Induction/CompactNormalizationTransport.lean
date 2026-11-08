import Langlands.Representation.Induction.SplitStagesComparison
import Langlands.Representation.Induction.CharacterTwistProof
import Langlands.Representation.Induction.SplitKernelCharacter

/-! # Naturality of compact induction normalization and subgroup transport -/

noncomputable section

universe u v w x y z t

namespace Langlands.Induction.CompactNormalizationTransport

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type v} [AddCommGroup V] [Module ℂ V]
  {W : Type w} [AddCommGroup W] [Module ℂ W]
  {X : Type x} [AddCommGroup X] [Module ℂ X]
  {Y : Type y} [AddCommGroup Y] [Module ℂ Y]
  {C : Type z} [AddCommGroup C] [Module ℂ C]
  {E : Type t} [AddCommGroup E] [Module ℂ E]

/-- Equality of inducing subgroups transports actual compact functions. -/
def subgroupCongr {H K : Subgroup G} (h : H = K) (σ : Representation ℂ H V) :
    (compactInduced H σ).Equiv
      (compactInduced K (σ.comp (MulEquiv.subgroupCongr h).symm.toMonoidHom)) := by
  subst K
  exact Representation.Equiv.refl _

/-- Subgroup transport followed by postcomposition of actual values. -/
def subgroupTransport {H K : Subgroup G} (h : H = K)
    (σ : Representation ℂ H V) (τ : Representation ℂ K W)
    (e : Representation.Equiv (σ.comp (MulEquiv.subgroupCongr h).symm.toMonoidHom) τ) :
    (compactInduced H σ).Equiv (compactInduced K τ) :=
  (subgroupCongr h σ).trans (compactInducedEquiv K e)

/-- Normalization of an existing compact-induction comparison by an ambient
character, subgroup transport and coefficient equivalence. -/
def normalizedTransport {H K : Subgroup G} (h : H = K)
    (ρ : Representation ℂ G X) (σ : Representation ℂ H V)
    (τ : Representation ℂ K W) (χ : SmoothCharacter ℂ G)
    (e0 : ρ.Equiv (compactInduced H σ))
    (e1 : Representation.Equiv
      ((Langlands.twist (χ.toMonoidHom.comp H.subtype) σ).comp
        (MulEquiv.subgroupCongr h).symm.toMonoidHom) τ) :
    (Langlands.twist χ.toMonoidHom ρ).Equiv (compactInduced K τ) :=
  (Langlands.twistEquiv χ.toMonoidHom e0).trans
    ((compactInductionTwistEquiv H χ σ).trans
      (subgroupTransport h _ τ e1))

/-- Natural integral and coefficient maps give a natural normalized
compact-induction comparison. -/
theorem normalizedTransport_natural {H K : Subgroup G} (h : H = K)
    (ρ : Representation ℂ G X) (ρ' : Representation ℂ G Y)
    (σ : Representation ℂ H V) (σ' : Representation ℂ H C)
    (τ : Representation ℂ K W) (τ' : Representation ℂ K E)
    (χ : SmoothCharacter ℂ G)
    (e0 : ρ.Equiv (compactInduced H σ))
    (e0' : ρ'.Equiv (compactInduced H σ'))
    (e1 : Representation.Equiv
      ((Langlands.twist (χ.toMonoidHom.comp H.subtype) σ).comp
        (MulEquiv.subgroupCongr h).symm.toMonoidHom) τ)
    (e1' : Representation.Equiv
      ((Langlands.twist (χ.toMonoidHom.comp H.subtype) σ').comp
        (MulEquiv.subgroupCongr h).symm.toMonoidHom) τ')
    (T : ρ.IntertwiningMap ρ') (S : σ.IntertwiningMap σ')
    (U : τ.IntertwiningMap τ')
    (h0 : ∀ a, e0' (T a) = compactInducedMap H S (e0 a))
    (h1 : ∀ a, e1' (S a) = U (e1 a)) (a : X) :
    normalizedTransport h ρ' σ' τ' χ e0' e1' (Langlands.twistIntertwining χ.toMonoidHom T a) =
      compactInducedMap K U (normalizedTransport h ρ σ τ χ e0 e1 a) := by
  subst K
  apply compactFunctions_eval_ext
  intro g
  change e1' ((χ.toMonoidHom g : ℂ) • eval H σ' (e0' (T a)).val g) =
    U (e1 ((χ.toMonoidHom g : ℂ) • eval H σ (e0 a).val g))
  rw [h0]
  change e1' ((χ.toMonoidHom g : ℂ) • S (eval H σ (e0 a).val g)) =
    U (e1 ((χ.toMonoidHom g : ℂ) • eval H σ (e0 a).val g))
  rw [map_smul, map_smul, map_smul, h1]

end Langlands.Induction.CompactNormalizationTransport
