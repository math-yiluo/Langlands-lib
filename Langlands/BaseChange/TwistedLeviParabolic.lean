import Langlands.BaseChange.TwistedPaleyWiener

/-!
# Standard parabolic subgroups of Levi products and their induced σ-intertwiners

For block shapes `B` and `C` of `n`, the subgroup `relParabolic E B C` of the Levi product
`∏ᵢ GL_{Bᵢ}(E)` consists of the elements whose block-diagonal matrix lies in the standard
parabolic of `C`, and `relProjection E B C` extracts the diagonal blocks of `C`. When `E` is a
field and `C` refines `B` (every partial sum of the block sizes of `B` is one of `C`) this
subgroup is the standard parabolic subgroup of the Levi product with Levi factor
`∏ⱼ GL_{Cⱼ}(E)`, and `relProjection E B C` is its Levi projection. The
entrywise action of an algebra automorphism `σ` preserves this subgroup and commutes with the
projection, which gives the induced σ-intertwiner of Rogawski (1988), §3, for smooth induction
inside a Levi product. See the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange

open GeneralLinear

universe u v uX

namespace TwistedLeviPaleyWiener

section Algebraic

variable {F : Type u} [CommRing F] (E : Type v) [CommRing E] [Algebra F E] {n : ℕ}

/-- The elements of the Levi product of `B` whose block-diagonal matrix lies in the standard
upper block parabolic of `C`. -/
def relParabolic (B C : BlockShape n) : Subgroup (B.Levi E) :=
  (C.parabolic E).comap (B.leviEmbedding E)

@[simp]
theorem mem_relParabolic (B C : BlockShape n) (g : B.Levi E) :
    g ∈ relParabolic E B C ↔ B.leviEmbedding E g ∈ C.parabolic E :=
  Iff.rfl

/-- The block-diagonal matrix of an element of `relParabolic E B C`, as an element of the
standard parabolic of `C`. -/
def relEmbedding (B C : BlockShape n) : relParabolic E B C →* C.parabolic E :=
  (B.leviEmbedding E).subgroupComap (C.parabolic E)

@[simp]
theorem relEmbedding_val (B C : BlockShape n) (g : relParabolic E B C) :
    (relEmbedding E B C g : GeneralLinear n E) = B.leviEmbedding E g :=
  rfl

/-- Extracts the diagonal blocks of `C` from the block-diagonal matrix of an element of
`relParabolic E B C`. For a refinement `C` of `B` over a field, this is the Levi projection of the
relative standard parabolic. -/
def relProjection (B C : BlockShape n) : relParabolic E B C →* C.Levi E :=
  (C.leviProjection E).comp (relEmbedding E B C)

theorem relProjection_apply (B C : BlockShape n) (g : relParabolic E B C) :
    relProjection E B C g = C.leviProjection E (relEmbedding E B C g) :=
  rfl

variable {E}

/-- The entrywise action of `σ` on the Levi product preserves `relParabolic E B C`. -/
theorem leviAut_mem_relParabolic_iff (σ : E ≃ₐ[F] E) (B C : BlockShape n) (g : B.Levi E) :
    leviAut σ B g ∈ relParabolic E B C ↔ g ∈ relParabolic E B C := by
  rw [mem_relParabolic, mem_relParabolic, ← entrywiseAut_leviEmbedding,
    entrywiseAut_mem_parabolic_iff]

/-- The projection `relProjection E B C` intertwines the entrywise actions of `σ`. -/
theorem relProjection_leviAut (σ : E ≃ₐ[F] E) (B C : BlockShape n)
    (x : relParabolic E B C) :
    relProjection E B C ⟨leviAut σ B x, (leviAut_mem_relParabolic_iff σ B C x).2 x.2⟩ =
      leviAut σ C (relProjection E B C x) := by
  have hemb : relEmbedding E B C ⟨leviAut σ B x, (leviAut_mem_relParabolic_iff σ B C x).2 x.2⟩ =
      ⟨entrywiseAut σ n (relEmbedding E B C x),
        (entrywiseAut_mem_parabolic_iff σ C _).2 (relEmbedding E B C x).2⟩ := by
    apply Subtype.ext
    change B.leviEmbedding E (leviAut σ B x) = entrywiseAut σ n (B.leviEmbedding E x)
    rw [entrywiseAut_leviEmbedding]
  rw [relProjection_apply, relProjection_apply, hemb, leviProjection_entrywiseAut]

end Algebraic

section Topology

variable {F : Type u} [CommRing F] [TopologicalSpace F]
  {E : Type v} [CommRing E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] {n : ℕ}

/-- The entrywise action of `σ` on a Levi product is continuous for the module topology. -/
theorem continuous_leviAut (σ : E ≃ₐ[F] E) (B : BlockShape n) : Continuous (leviAut σ B) :=
  continuous_pi fun i =>
    (continuous_entrywiseAut_of_isModuleTopology σ (B.size i)).comp (continuous_apply i)

/-- The inverse entrywise action of `σ` on a Levi product is continuous. -/
theorem continuous_leviAut_symm (σ : E ≃ₐ[F] E) (B : BlockShape n) :
    Continuous (leviAut σ B).symm :=
  continuous_pi fun i =>
    (continuous_entrywiseAut_of_isModuleTopology σ.symm (B.size i)).comp (continuous_apply i)

end Topology

section Induced

variable {F : Type u} [CommRing F] [TopologicalSpace F]
  {E : Type v} [CommRing E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
  [IsModuleTopology F E] {n : ℕ}

/-- The σ-intertwiner `(ι B f)(g) = BΞ (f (σ⁻¹ g))` of the unnormalized smooth induction
`Ind_{P}^{M_B} (Ξ ∘ p)` from the parabolic `P = relParabolic E B C` of the Levi product of `B`
along its projection `p` to the Levi product of `C`, for a σ-intertwiner `BΞ : Ξ ≅ Ξ^σ` of a
representation of the Levi product of `C` (Rogawski 1988, §3; Henniart–Lemaire 2011, II.4.4). It
is `inducedTwistedIntertwiner` for the entrywise action `leviAut σ B`. -/
def relInducedSigmaIntertwiner (σ : E ≃ₐ[F] E) (B C : BlockShape n) {X : Type uX}
    [AddCommGroup X] [Module ℂ X] (Ξ : Representation ℂ (C.Levi E) X)
    (BΞ : Ξ.Equiv (Ξ.comp (leviAut σ C).toMonoidHom)) :
    (Induction.smoothInduced (relParabolic E B C) (Ξ.comp (relProjection E B C))).Equiv
      ((Induction.smoothInduced (relParabolic E B C) (Ξ.comp (relProjection E B C))).comp
        (leviAut σ B).toMonoidHom) :=
  inducedTwistedIntertwiner (leviAut σ B) (continuous_leviAut σ B) (continuous_leviAut_symm σ B)
    (relParabolic E B C) (leviAut_mem_relParabolic_iff σ B C) (relProjection E B C)
    (leviAut σ C) (relProjection_leviAut σ B C) Ξ BΞ

theorem eval_relInducedSigmaIntertwiner (σ : E ≃ₐ[F] E) (B C : BlockShape n) {X : Type uX}
    [AddCommGroup X] [Module ℂ X] (Ξ : Representation ℂ (C.Levi E) X)
    (BΞ : Ξ.Equiv (Ξ.comp (leviAut σ C).toMonoidHom))
    (f : Induction.SmoothFunctions (relParabolic E B C) (Ξ.comp (relProjection E B C)))
    (g : B.Levi E) :
    Induction.eval _ _ (relInducedSigmaIntertwiner σ B C Ξ BΞ f) g =
      BΞ (Induction.eval _ _ f ((leviAut σ B).symm g)) :=
  rfl

end Induced

end TwistedLeviPaleyWiener

end Langlands.BaseChange
