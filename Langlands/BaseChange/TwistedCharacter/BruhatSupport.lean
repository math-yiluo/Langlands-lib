import Langlands.BaseChange.TwistedLeviParabolic
import Langlands.Group.GL.Maps
import Langlands.Representation.Geometric.SmoothSupportFiltration

/-! # Stability of double-coset support under twisted induction -/

noncomputable section

namespace Langlands.Geometric.OrderedDoubleCosets

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {P Q : Subgroup G} {m : ℕ} (s : OrderedDoubleCosets P Q m)

omit [IsTopologicalGroup G] in
/-- Applying an automorphism that preserves both subgroups and fixes the representatives
preserves every initial orbit union. -/
theorem quotientMap_mem_initialOrbits_automorphism (θ : G ≃* G)
    (hP : ∀ g, θ g ∈ P ↔ g ∈ P) (hQ : ∀ g, θ g ∈ Q ↔ g ∈ Q)
    (hw : ∀ i, θ (s.representative i) = s.representative i)
    {k : Fin (m + 1)} {g : G}
    (hg : Induction.quotientMap P g ∈ s.initialOrbits k) :
    Induction.quotientMap P (θ g) ∈ s.initialOrbits k := by
  obtain ⟨i, hi, q, hq⟩ := hg
  refine ⟨i, hi, ⟨θ q, (hQ q).2 q.property⟩, ?_⟩
  apply Quotient.sound
  apply QuotientGroup.rightRel_apply.mpr
  have hmem : g * ((s.representative i)⁻¹ * (q : G))⁻¹ ∈ P :=
    QuotientGroup.rightRel_apply.mp (Quotient.exact hq)
  change θ g * ((s.representative i)⁻¹ * θ q)⁻¹ ∈ P
  simpa only [map_mul, map_inv, hw] using (hP _).2 hmem

variable {V : Type uV} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ P V)

/-- The linear operator on smooth sections preserves each step of the actual
double-coset support filtration. -/
def SmoothInductionSupportPreservation
    (L : Module.End ℂ (Induction.SmoothFunctions P ρ)) : Prop :=
  ∀ (k : Fin (m + 1)) (f : Induction.SmoothFunctions P ρ),
    f ∈ (s.rawSmoothSupportFiltration.step k).obj (Rep.of ρ) →
      L f ∈ (s.rawSmoothSupportFiltration.step k).obj (Rep.of ρ)

/-- A coefficient operator together with inverse pullback preserves each support
step when the automorphism fixes the representatives. -/
theorem smoothInductionSupportPreservation_of_eval (θ : G ≃* G)
    (hP : ∀ g, θ g ∈ P ↔ g ∈ P) (hQ : ∀ g, θ g ∈ Q ↔ g ∈ Q)
    (hw : ∀ i, θ (s.representative i) = s.representative i)
    (A : Module.End ℂ V) (L : Module.End ℂ (Induction.SmoothFunctions P ρ))
    (hL : ∀ f g, Induction.eval P ρ (L f) g = A (Induction.eval P ρ f (θ.symm g))) :
    s.SmoothInductionSupportPreservation ρ L := by
  intro k f hf g hg
  have hg' : Induction.eval P ρ f (θ.symm g) ≠ 0 := by
    intro h
    apply hg
    rw [hL, h, map_zero]
  simpa only [MulEquiv.apply_symm_apply] using
    s.quotientMap_mem_initialOrbits_automorphism θ hP hQ hw (hf (θ.symm g) hg')

/-- A linear map intertwining two endomorphisms takes a preserved support step to a
preserved image step. The quotient projection for Jacquet modules is one such map. -/
theorem mapsTo_smoothSupportImage_of_eval (θ : G ≃* G)
    (hP : ∀ g, θ g ∈ P ↔ g ∈ P) (hQ : ∀ g, θ g ∈ Q ↔ g ∈ Q)
    (hw : ∀ i, θ (s.representative i) = s.representative i)
    (A : Module.End ℂ V) (L : Module.End ℂ (Induction.SmoothFunctions P ρ))
    (hL : ∀ f g, Induction.eval P ρ (L f) g = A (Induction.eval P ρ f (θ.symm g)))
    {W : Type*} [AddCommGroup W] [Module ℂ W] (q : Induction.SmoothFunctions P ρ →ₗ[ℂ] W)
    (J : Module.End ℂ W) (hJ : ∀ f, J (q f) = q (L f)) (k : Fin (m + 1)) :
    let S := ((s.rawSmoothSupportFiltration.step k).obj (Rep.of ρ)).toSubmodule.map q
    Set.MapsTo J S S := by
  dsimp only
  intro x hx
  obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hx
  rw [hJ]
  exact Submodule.mem_map.mpr
    ⟨L f, s.smoothInductionSupportPreservation_of_eval ρ θ hP hQ hw A L hL k f hf, rfl⟩

end Langlands.Geometric.OrderedDoubleCosets

namespace Langlands.BaseChange

open GeneralLinear Geometric TwistedLeviPaleyWiener

universe u v z

variable {F : Type u} [CommRing F] {E : Type v} [CommRing E] [Algebra F E]
  {n : ℕ} (σ : E ≃ₐ[F] E)

@[simp]
theorem entrywiseAut_permutation (w : Equiv.Perm (Fin n)) :
    entrywiseAut σ n (permutation n E w) = permutation n E w := by
  ext i j
  rw [entrywiseAut_apply_apply, permutation_entry]
  split <;> simp

/-- A representative in a block Levi that embeds as a permutation matrix is
fixed by entrywise field action. -/
theorem leviAut_eq_self_of_leviEmbedding_eq_permutation (B : BlockShape n)
    {g : B.Levi E} {w : Equiv.Perm (Fin n)}
    (hg : B.leviEmbedding E g = permutation n E w) :
    leviAut σ B g = g := by
  apply B.leviEmbedding_injective E
  rw [← entrywiseAut_leviEmbedding, hg, entrywiseAut_permutation]

variable [TopologicalSpace F] [TopologicalSpace E] [IsTopologicalRing E]
  [IsModuleTopology F E] {B C D : BlockShape n} {m : ℕ}

/-- The relative induction σ-operator preserves the filtration by support in initial
double cosets whose representatives are block permutation matrices. -/
theorem relInducedSigmaIntertwiner_preserves_support
    (s : OrderedDoubleCosets (relParabolic E B C) (relParabolic E B D) m)
    (hw : ∀ i, ∃ w, B.leviEmbedding E (s.representative i) = permutation n E w)
    {X : Type z} [AddCommGroup X] [Module ℂ X] (Ξ : Representation ℂ (C.Levi E) X)
    (A : Ξ.Equiv (Ξ.comp (leviAut σ C).toMonoidHom)) :
    s.SmoothInductionSupportPreservation (Ξ.comp (relProjection E B C))
      (relInducedSigmaIntertwiner σ B C Ξ A).toLinearMap :=
  s.smoothInductionSupportPreservation_of_eval _ (leviAut σ B)
    (leviAut_mem_relParabolic_iff σ B C) (leviAut_mem_relParabolic_iff σ B D)
    (fun i => let ⟨_, hi⟩ := hw i; leviAut_eq_self_of_leviEmbedding_eq_permutation σ B hi)
    A.toLinearMap _ (eval_relInducedSigmaIntertwiner σ B C Ξ A)

end Langlands.BaseChange
