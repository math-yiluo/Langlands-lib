import Langlands.BaseChange.SigmaInducedIntertwiner
import Langlands.BaseChange.PseudoCoefficient
import Langlands.Representation.Jacquet.Parabolic
import Langlands.Representation.Parabolic.LeviBridges

/-!
# The σ-intertwiner on a Jacquet module

Rogawski (1988), §3: an intertwiner for an automorphism preserving a parabolic subgroup
acts on the corresponding Jacquet quotient by sending `[v]` to `[A v]`. This module
constructs that map on the Library's actual coinvariants and gives the σ-intertwiner for
the unnormalized Jacquet module of a standard block parabolic of `GL_n`.
-/

noncomputable section

namespace Langlands.Jacquet

universe uR uG uV

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module R V]

private def twistedCoinvariantsMap (ρ : Representation R G V) (N : Subgroup G)
    (θ : G ≃* G) (hN : ∀ g, θ g ∈ N ↔ g ∈ N) (A : V →ₗ[R] V)
    (hA : ∀ g v, A (ρ g v) = ρ (θ g) (A v)) : Coinvariants ρ N →ₗ[R] Coinvariants ρ N :=
  lift ρ N ((mk ρ N).comp A) (by
    intro n
    ext v
    change mk ρ N (A (ρ n v)) = mk ρ N (A v)
    rw [hA]
    exact mk_apply_subgroup ρ N ⟨θ n, (hN n).2 n.2⟩ (A v))

private theorem symm_preserves (N : Subgroup G) (θ : G ≃* G)
    (hN : ∀ g, θ g ∈ N ↔ g ∈ N) (g : G) : θ.symm g ∈ N ↔ g ∈ N := by
  simpa only [MulEquiv.apply_symm_apply] using (hN (θ.symm g)).symm

private theorem symm_intertwines (ρ : Representation R G V) (θ : G ≃* G) (A : V ≃ₗ[R] V)
    (hA : ∀ g v, A (ρ g v) = ρ (θ g) (A v)) (g : G) (v : V) :
    A.symm (ρ g v) = ρ (θ.symm g) (A.symm v) := by
  apply A.injective
  rw [A.apply_symm_apply, hA, θ.apply_symm_apply, A.apply_symm_apply]

/-- A linear isomorphism intertwining `ρ` with `ρ ∘ θ` descends to a linear isomorphism
of the `N`-coinvariants by `[v] ↦ [A v]`, when `θ` preserves `N`. -/
def twistedCoinvariantsEquiv (ρ : Representation R G V) (N : Subgroup G)
    (θ : G ≃* G) (hN : ∀ g, θ g ∈ N ↔ g ∈ N) (A : V ≃ₗ[R] V)
    (hA : ∀ g v, A (ρ g v) = ρ (θ g) (A v)) : Coinvariants ρ N ≃ₗ[R] Coinvariants ρ N :=
  LinearEquiv.ofLinearMap
    (twistedCoinvariantsMap ρ N θ hN A.toLinearMap hA)
    (twistedCoinvariantsMap ρ N θ.symm (symm_preserves N θ hN) A.symm.toLinearMap
      (symm_intertwines ρ θ A hA))
    (by
      apply LinearMap.ext
      intro q
      obtain ⟨v, rfl⟩ := mk_surjective ρ N q
      change mk ρ N (A (A.symm v)) = mk ρ N v
      rw [A.apply_symm_apply])
    (by
      apply LinearMap.ext
      intro q
      obtain ⟨v, rfl⟩ := mk_surjective ρ N q
      change mk ρ N (A.symm (A v)) = mk ρ N v
      rw [A.symm_apply_apply])

@[simp]
theorem twistedCoinvariantsEquiv_mk (ρ : Representation R G V) (N : Subgroup G)
    (θ : G ≃* G) (hN : ∀ g, θ g ∈ N ↔ g ∈ N) (A : V ≃ₗ[R] V)
    (hA : ∀ g v, A (ρ g v) = ρ (θ g) (A v)) (v : V) :
    twistedCoinvariantsEquiv ρ N θ hN A hA (mk ρ N v) = mk ρ N (A v) :=
  rfl

end Langlands.Jacquet

namespace Langlands.BaseChange

open GeneralLinear

universe uF uE uW

variable {F : Type uF} [CommRing F] {E : Type uE} [CommRing E] [Algebra F E]
  {n : ℕ} (σ : E ≃ₐ[F] E) (B : BlockShape n)

/-- The σ-action on the parabolic preserves the kernel of the Levi projection. -/
theorem parabolicAut_mem_unipotentRadical_iff (p : B.parabolic E) :
    parabolicAut σ B p ∈ B.unipotentRadical E ↔ p ∈ B.unipotentRadical E := by
  change B.leviProjection E (parabolicAut σ B p) = 1 ↔ B.leviProjection E p = 1
  rw [show B.leviProjection E (parabolicAut σ B p) = leviAut σ B (B.leviProjection E p)
    from leviProjection_entrywiseAut σ B p]
  constructor
  · intro h
    exact (leviAut σ B).injective (h.trans (map_one _).symm)
  · intro h
    rw [h, map_one]

variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- A σ-intertwiner of a `GL_n(E)` representation descends to a σ-intertwiner of its
unnormalized Jacquet module on the product Levi, with formula `[v] ↦ [A v]`
(Rogawski 1988, §3, printed p. 218). -/
def jacquetSigmaIntertwiner {ρ : Representation ℂ (GeneralLinear n E) W}
    (A : SigmaIntertwiner σ n ρ) :
    (Parabolic.leviCoinvariants B (ρ.comp (B.parabolic E).subtype)).Equiv
      ((Parabolic.leviCoinvariants B (ρ.comp (B.parabolic E).subtype)).comp
        (leviAut σ B).toMonoidHom) :=
  Representation.Equiv.mk
    (Jacquet.twistedCoinvariantsEquiv (ρ.comp (B.parabolic E).subtype) (B.unipotentRadical E)
      (parabolicAut σ B) (parabolicAut_mem_unipotentRadical_iff σ B) A.toLinearEquiv
      (fun p v => Representation.IntertwiningMap.isIntertwining _ _ A.toIntertwiningMap p v))
    (by
      intro m
      apply LinearMap.ext
      intro q
      obtain ⟨v, rfl⟩ := B.jacquetMk_surjective ρ q
      change B.jacquetMk ρ (A (ρ (B.leviEmbedding E m) v)) =
        B.jacquetMk ρ (ρ (B.leviEmbedding E (leviAut σ B m)) (A v))
      rw [← entrywiseAut_leviEmbedding]
      exact congrArg (B.jacquetMk ρ)
        (Representation.IntertwiningMap.isIntertwining _ _ A.toIntertwiningMap _ v))

@[simp]
theorem jacquetSigmaIntertwiner_mk {ρ : Representation ℂ (GeneralLinear n E) W}
    (A : SigmaIntertwiner σ n ρ) (v : W) :
    jacquetSigmaIntertwiner σ B A (B.jacquetMk ρ v) = B.jacquetMk ρ (A v) :=
  rfl

end Langlands.BaseChange
