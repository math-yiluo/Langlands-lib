import Langlands.Representation.Jacquet.CanonicalLiftIntertwinerNaturalityStatement

noncomputable section

namespace Langlands.Jacquet

universe uG uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

theorem compressedAction_pow_natural
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (hρ : IsSmooth ρ) (hσ : IsSmooth σ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (g : G) (f : ρ.IntertwiningMap σ) (r : ℕ)
    (v : fixedVectors ρ K.toSubgroup) :
    fixedVectorsMap f K.toSubgroup ((compressedAction ρ hρ K hK g ^ r) v) =
      (compressedAction σ hσ K hK g ^ r) (fixedVectorsMap f K.toSubgroup v) := by
  induction r with
  | zero => rfl
  | succ r ih =>
      simp only [pow_succ', Module.End.mul_apply]
      have h := LinearMap.congr_fun (compressedAction_natural ρ σ hρ hσ K hK g f)
        ((compressedAction ρ hρ K hK g ^ r) v)
      exact h.trans (congrArg (compressedAction σ hσ K hK g) ih)

theorem fixedVectorsMap_mem_stableImage
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (hρ : IsSmooth ρ) (hσ : IsSmooth σ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (g : G) (f : ρ.IntertwiningMap σ)
    (v : fixedVectors ρ K.toSubgroup) (hv : v ∈ stableImage ρ hρ K hK g) :
    fixedVectorsMap f K.toSubgroup v ∈ stableImage σ hσ K hK g := by
  rw [mem_stableImage] at hv ⊢
  intro r
  obtain ⟨w, hw⟩ := hv r
  refine ⟨fixedVectorsMap f K.toSubgroup w, ?_⟩
  rw [← compressedAction_pow_natural ρ σ hρ hσ K hK g f r w, hw]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem fixedJacquetMap_natural
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (K : Subgroup G) (N M : Subgroup G) (hMN : M ≤ Subgroup.normalizer N)
    (f : ρ.IntertwiningMap σ) (v : fixedVectors ρ K) :
    fixedJacquetMap σ N M hMN K (fixedVectorsMap f K v) =
      fixedVectorsMap (map N M hMN f) (K.comap M.subtype)
        (fixedJacquetMap ρ N M hMN K v) := by
  apply Subtype.ext
  exact (map_mk N M hMN f (v : V)).symm

theorem inverseCanonicalLift_natural
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (hρ : IsSmooth ρ) (hσ : IsSmooth σ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (g : G) (f : ρ.IntertwiningMap σ)
    (N M : Subgroup G) (hMN : M ≤ Subgroup.normalizer N)
    (hρbij : Function.Bijective (stableImageJacquetMap ρ hρ K hK g N M hMN))
    (hσbij : Function.Bijective (stableImageJacquetMap σ hσ K hK g N M hMN))
    (j : fixedVectors (action ρ N M hMN) (K.toSubgroup.comap M.subtype)) :
    f (stableImageToRepresentation ρ hρ K hK g
        ((LinearEquiv.ofBijective (stableImageJacquetMap ρ hρ K hK g N M hMN)
          hρbij).symm j)) =
      stableImageToRepresentation σ hσ K hK g
        ((LinearEquiv.ofBijective (stableImageJacquetMap σ hσ K hK g N M hMN)
          hσbij).symm
            (fixedVectorsMap (map N M hMN f) (K.toSubgroup.comap M.subtype) j)) := by
  let u := (LinearEquiv.ofBijective (stableImageJacquetMap ρ hρ K hK g N M hMN)
    hρbij).symm j
  have hu : stableImageJacquetMap ρ hρ K hK g N M hMN u = j :=
    (LinearEquiv.ofBijective (stableImageJacquetMap ρ hρ K hK g N M hMN)
      hρbij).apply_symm_apply j
  let w : stableImage σ hσ K hK g :=
    ⟨fixedVectorsMap f K.toSubgroup u.val,
      fixedVectorsMap_mem_stableImage ρ σ hρ hσ K hK g f u.val u.property⟩
  have hw : stableImageJacquetMap σ hσ K hK g N M hMN w =
      fixedVectorsMap (map N M hMN f) (K.toSubgroup.comap M.subtype) j := by
    change fixedJacquetMap σ N M hMN K.toSubgroup
        (fixedVectorsMap f K.toSubgroup u.val) = _
    rw [fixedJacquetMap_natural]
    change fixedVectorsMap (map N M hMN f) (K.toSubgroup.comap M.subtype)
      (stableImageJacquetMap ρ hρ K hK g N M hMN u) = _
    rw [hu]
  have heq : w =
      (LinearEquiv.ofBijective (stableImageJacquetMap σ hσ K hK g N M hMN)
        hσbij).symm
          (fixedVectorsMap (map N M hMN f) (K.toSubgroup.comap M.subtype) j) := by
    apply hσbij.1
    exact hw.trans
      ((LinearEquiv.ofBijective (stableImageJacquetMap σ hσ K hK g N M hMN)
        hσbij).apply_symm_apply _).symm
  change stableImageToRepresentation σ hσ K hK g w = _
  exact congrArg (stableImageToRepresentation σ hσ K hK g) heq

/-- Naturality of the existing stable images, quotient maps, and conditional
inverse canonical lifts under arbitrary representation intertwiners. -/
theorem canonicalLiftIntertwinerNaturality :
    CanonicalLiftIntertwinerNaturalityStatement.{uG, uV, uW} := by
  intro G _ _ _ V _ _ W _ _ ρ σ hρ hσ K hK g f
  constructor
  · exact fixedVectorsMap_mem_stableImage ρ σ hρ hσ K hK g f
  · intro N M hMN
    constructor
    · exact fixedJacquetMap_natural ρ σ K.toSubgroup N M hMN f
    · exact inverseCanonicalLift_natural ρ σ hρ hσ K hK g f N M hMN

end Langlands.Jacquet
