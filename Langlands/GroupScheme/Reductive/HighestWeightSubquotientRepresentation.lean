import Langlands.GroupScheme.Reductive.HighestWeightSubquotient
import Langlands.GroupScheme.MatrixRepresentation.NormalFixedRepresentation

/-! # The highest-weight subquotient representation -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- An intertwiner with a left inverse reflects character vectors. -/
theorem Intertwines.mem_characterSpace_of_leftInverse {ρ : MatrixRepresentation G n}
    {σ : MatrixRepresentation G m} {C : Matrix m n k} (hC : Intertwines ρ σ C)
    {C' : Matrix n m k} (hC' : C' * C = 1) {χ : rationalCharacters G} {v : n → k}
    (hv : C *ᵥ v ∈ σ.characterSpace χ) : v ∈ ρ.characterSpace χ := by
  apply (mem_characterSpace_iff_affine _ _ _).mpr
  intro A x
  have h := characterSpace_affine hv A x
  have hcv : (fun r => algebraMap k A ((C *ᵥ v) r)) =
      C.map (algebraMap k A) *ᵥ (fun r => algebraMap k A (v r)) := by
    funext r
    exact (algebraMap k A).map_mulVec C v r
  have hinv : C'.map (algebraMap k A) * C.map (algebraMap k A) = 1 := by
    rw [← Matrix.map_mul, hC', Matrix.map_one _ (map_zero _) (map_one _)]
  rw [hcv, Matrix.mulVec_mulVec, ← hC A x, ← Matrix.mulVec_mulVec] at h
  have h2 := congrArg (fun w => C'.map (algebraMap k A) *ᵥ w) h
  simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hinv, Matrix.one_mul,
    Matrix.mulVec_smul] at h2
  rw [Matrix.one_mulVec] at h2
  exact h2

end Langlands.GroupScheme.MatrixRepresentation

namespace Langlands.GroupScheme.SplitPinning

open MatrixRepresentation

variable {F : Type u} [Field F]
  {H : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom H.X.hom]
  (p : SplitPinning H) {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

theorem Intertwines.restrict_inclusion {ρ : MatrixRepresentation H n}
    {σ : MatrixRepresentation H m} {C : Matrix m n F} (hC : Intertwines ρ σ C) :
    Intertwines (ρ.restrict p.inclusion) (σ.restrict p.inclusion) C := by
  intro A x
  rw [affineMatrix_restrict, affineMatrix_restrict]
  exact hC A _

/-- Intertwiners map weight spaces into weight spaces. -/
theorem Intertwines.mulVec_mem_weightSpace {ρ : MatrixRepresentation H n}
    {σ : MatrixRepresentation H m} {C : Matrix m n F} (hC : Intertwines ρ σ C)
    {mu : characterLattice p.torus} {v : n → F} (hv : v ∈ p.representationWeightSpace ρ mu) :
    C *ᵥ v ∈ p.representationWeightSpace σ mu := by
  let := p.isSplitTorus.isAffineHom
  exact MatrixRepresentation.Intertwines.mulVec_mem_characterSpace
    (Intertwines.restrict_inclusion p hC) hv

/-- An intertwiner with a left inverse reflects weight vectors. -/
theorem Intertwines.mem_weightSpace_of_leftInverse {ρ : MatrixRepresentation H n}
    {σ : MatrixRepresentation H m} {C : Matrix m n F} (hC : Intertwines ρ σ C)
    {C' : Matrix n m F} (hC' : C' * C = 1) {mu : characterLattice p.torus} {v : n → F}
    (hv : C *ᵥ v ∈ p.representationWeightSpace σ mu) :
    v ∈ p.representationWeightSpace ρ mu := by
  let := p.isSplitTorus.isAffineHom
  exact MatrixRepresentation.Intertwines.mem_characterSpace_of_leftInverse
    (Intertwines.restrict_inclusion p hC) hC' hv

theorem Intertwines.map_weightSpace_le {ρ : MatrixRepresentation H n}
    {σ : MatrixRepresentation H m} {C : Matrix m n F} (hC : Intertwines ρ σ C)
    (mu : characterLattice p.torus) :
    (p.representationWeightSpace ρ mu).map C.mulVecLin ≤ p.representationWeightSpace σ mu := by
  rintro _ ⟨v, hv, rfl⟩
  exact Intertwines.mulVec_mem_weightSpace p hC hv

/-- A surjective intertwiner maps weight spaces onto weight spaces. -/
theorem Intertwines.map_weightSpace_eq_of_surjective {ρ : MatrixRepresentation H n}
    {σ : MatrixRepresentation H m} {C : Matrix m n F} (hC : Intertwines ρ σ C)
    (hsurj : Function.Surjective C.mulVecLin) (mu : characterLattice p.torus) :
    p.representationWeightSpace σ mu = (p.representationWeightSpace ρ mu).map C.mulVecLin := by
  refine (iSupIndep_representationWeightSpace (p := p) σ).eq_of_le_of_iSup_eq_top
    (U := fun mu => (p.representationWeightSpace ρ mu).map C.mulVecLin)
    (fun mu => Intertwines.map_weightSpace_le p hC mu) ?_ mu
  rw [← Submodule.map_iSup, p.iSup_representationWeightSpace_eq_top ρ, Submodule.map_top,
    LinearMap.range_eq_top.mpr hsurj]

/-- An intertwiner with a left inverse maps a weight space onto the intersection of the target
weight space with its range. -/
theorem Intertwines.map_weightSpace_eq_inf_range {ρ : MatrixRepresentation H n}
    {σ : MatrixRepresentation H m} {C : Matrix m n F} (hC : Intertwines ρ σ C)
    {C' : Matrix n m F} (hC' : C' * C = 1) (mu : characterLattice p.torus) :
    (p.representationWeightSpace ρ mu).map C.mulVecLin =
      p.representationWeightSpace σ mu ⊓ LinearMap.range C.mulVecLin := by
  apply le_antisymm
  · exact le_inf (Intertwines.map_weightSpace_le p hC mu) LinearMap.map_le_range
  · rintro _ ⟨hw, ⟨v, rfl⟩⟩
    exact ⟨v, Intertwines.mem_weightSpace_of_leftInverse p hC hC' hw, rfl⟩

omit [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] in
/-- A linear map injective on a subspace preserves its dimension. -/
theorem finrank_map_of_disjoint {V W : Type*} [AddCommGroup V] [Module F V] [AddCommGroup W]
    [Module F W] [FiniteDimensional F V] (f : V →ₗ[F] W) (S : Submodule F V)
    (hd : S ⊓ LinearMap.ker f = ⊥) : Module.finrank F (S.map f) = Module.finrank F S := by
  have hinj : Function.Injective (f.domRestrict S) := by
    intro a b h
    apply Subtype.ext
    have hmem : (a : V) - b ∈ S ⊓ LinearMap.ker f := by
      refine Submodule.mem_inf.mpr ⟨S.sub_mem a.2 b.2, ?_⟩
      rw [LinearMap.mem_ker, map_sub, sub_eq_zero]
      exact h
    rw [hd, Submodule.mem_bot, sub_eq_zero] at hmem
    exact hmem
  rw [← LinearMap.range_domRestrict, LinearMap.finrank_range_of_inj hinj]

/-- Split coordinates of the subquotient `X/Y` attached to a weight `nu`: a subrepresentation on
`X` and its quotient by `Y`. -/
structure HighestSubquotientData (ρ : MatrixRepresentation H n) (nu : characterLattice p.torus)
    where
  d : ℕ
  r : ℕ
  sub : MatrixRepresentation H (Fin d)
  quot : MatrixRepresentation H (Fin r)
  incl : Matrix n (Fin d) F
  retr : Matrix (Fin d) n F
  proj : Matrix (Fin r) (Fin d) F
  sect : Matrix (Fin d) (Fin r) F
  retr_incl : retr * incl = 1
  incl_intertwines : Intertwines sub ρ incl
  range_incl : LinearMap.range incl.mulVecLin = p.highestGenerated ρ nu
  proj_sect : proj * sect = 1
  ker_proj : LinearMap.ker proj.mulVecLin = (p.highestRadical ρ nu).comap incl.mulVecLin
  proj_intertwines : Intertwines sub quot proj

/-- The subquotient coordinates exist. -/
theorem nonempty_highestSubquotientData (ρ : MatrixRepresentation H n)
    (nu : characterLattice p.torus) : Nonempty (p.HighestSubquotientData ρ nu) := by
  obtain ⟨d, B, C, hCB, hcols, hproj⟩ :=
    exists_subspace_split_coordinates (p.highestGenerated ρ nu)
  have hstable := (p.isStableSubspace_highestGenerated ρ nu).isStableCoordinates B C hcols hproj
  have hB : Intertwines (restrictCoordinates ρ B C hCB hstable) ρ B :=
    intertwines_restrictCoordinates ρ B C hCB hstable
  have hrange := range_coordinateInclusion_eq _ B C hcols hproj
  have hY := (p.isStableSubspace_highestRadical ρ nu).comap hB
  obtain ⟨q⟩ := nonempty_quotientRepresentation _ _ hY
  exact ⟨⟨d, q.dimension, _, q.representation, B, C, q.projection, q.sectionMap, hCB, hB,
    hrange, q.right_inverse, q.ker_projection, q.intertwines⟩⟩

variable {p} {ρ : MatrixRepresentation H n} {nu : characterLattice p.torus}

/-- The subquotient `X/Y` of a weight `nu` of multiplicity one which dominates all weights is
an irreducible representation of highest weight `nu`. -/
theorem HighestSubquotientData.isHighestWeight (D : p.HighestSubquotientData ρ nu)
    (hmult : Module.finrank F (p.representationWeightSpace ρ nu) = 1)
    (hmax : ∀ mu, p.representationWeightSpace ρ mu ≠ ⊥ → nu - mu ∈ p.positiveRootMonoid) :
    p.IsHighestWeight D.quot nu := by
  have hinj : Function.Injective D.incl.mulVecLin :=
    coordinateInclusion_injective (R := CommRingCat.of F) D.incl D.retr D.retr_incl
  have hsurj : Function.Surjective D.proj.mulVecLin := by
    intro v
    refine ⟨D.sect *ᵥ v, ?_⟩
    change D.proj *ᵥ (D.sect *ᵥ v) = v
    rw [Matrix.mulVec_mulVec, D.proj_sect, Matrix.one_mulVec]
  have hsub : ∀ mu, (p.representationWeightSpace D.sub mu).map D.incl.mulVecLin =
      p.representationWeightSpace ρ mu ⊓ p.highestGenerated ρ nu := fun mu => by
    rw [Intertwines.map_weightSpace_eq_inf_range p D.incl_intertwines D.retr_incl, D.range_incl]
  have hquot : ∀ mu, p.representationWeightSpace D.quot mu =
      (p.representationWeightSpace D.sub mu).map D.proj.mulVecLin := fun mu =>
    Intertwines.map_weightSpace_eq_of_surjective p D.proj_intertwines hsurj mu
  -- the `nu` weight space of the subrepresentation is a line meeting `ker proj` trivially
  have hsubnu : (p.representationWeightSpace D.sub nu).map D.incl.mulVecLin =
      p.representationWeightSpace ρ nu := by
    rw [hsub, inf_eq_left.mpr (p.weightSpace_le_highestGenerated ρ nu)]
  have hfin_sub : Module.finrank F (p.representationWeightSpace D.sub nu) = 1 := by
    rw [← hmult, ← hsubnu, finrank_map_of_disjoint _ _ (by
      rw [LinearMap.ker_eq_bot.mpr hinj, inf_bot_eq])]
  have hdisj : p.representationWeightSpace D.sub nu ⊓ LinearMap.ker D.proj.mulVecLin = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    obtain ⟨hu, hk⟩ := Submodule.mem_inf.mp hu
    rw [D.ker_proj, Submodule.mem_comap] at hk
    have hu' : D.incl.mulVecLin u ∈ p.representationWeightSpace ρ nu := by
      rw [← hsubnu]
      exact ⟨u, hu, rfl⟩
    have h0 : D.incl.mulVecLin u ∈ p.highestRadical ρ nu ⊓ p.representationWeightSpace ρ nu :=
      Submodule.mem_inf.mpr ⟨hk, hu'⟩
    rw [p.highestRadical_inf_weightSpace ρ nu, Submodule.mem_bot] at h0
    rw [Submodule.mem_bot]
    exact hinj (h0.trans (map_zero _).symm)
  have hfin_quot : Module.finrank F (p.representationWeightSpace D.quot nu) = 1 := by
    rw [hquot, finrank_map_of_disjoint _ _ hdisj, hfin_sub]
  have hnt : Nontrivial (Fin D.r → F) := by
    by_contra h
    have : Subsingleton (Fin D.r → F) := not_nontrivial_iff_subsingleton.mp h
    have h0 : Module.finrank F (p.representationWeightSpace D.quot nu) = 0 := by
      rw [Module.finrank_zero_iff]
      infer_instance
    omega
  refine ⟨⟨hnt, fun W hW => ?_⟩, p.iSup_representationWeightSpace_eq_top D.quot,
    hfin_quot, fun mu hmu => ?_⟩
  · -- irreducibility
    have hW' := hW.comap D.proj_intertwines
    have hV := hW'.map D.incl_intertwines
    have hVX : (W.comap D.proj.mulVecLin).map D.incl.mulVecLin ≤ p.highestGenerated ρ nu := by
      rw [← D.range_incl]
      exact LinearMap.map_le_range
    have hYV : p.highestRadical ρ nu ≤ (W.comap D.proj.mulVecLin).map D.incl.mulVecLin := by
      intro y hy
      have hyX : y ∈ LinearMap.range D.incl.mulVecLin := by
        rw [D.range_incl]
        exact p.highestRadical_le ρ nu hy
      obtain ⟨u, rfl⟩ := hyX
      refine ⟨u, ?_, rfl⟩
      show D.proj.mulVecLin u ∈ W
      have hk : u ∈ LinearMap.ker D.proj.mulVecLin := by
        rw [D.ker_proj, Submodule.mem_comap]
        exact hy
      rw [LinearMap.mem_ker] at hk
      rw [hk]
      exact W.zero_mem
    rcases p.eq_highestRadical_or_eq_highestGenerated ρ nu hmult hV hYV hVX with h | h
    · left
      have hW'eq : W.comap D.proj.mulVecLin = LinearMap.ker D.proj.mulVecLin := by
        apply Submodule.map_injective_of_injective hinj
        rw [h, D.ker_proj, Submodule.map_comap_eq, D.range_incl,
          inf_eq_right.mpr (p.highestRadical_le ρ nu)]
      rw [eq_bot_iff]
      intro w hw
      obtain ⟨u, rfl⟩ := hsurj w
      have : u ∈ W.comap D.proj.mulVecLin := hw
      rw [hW'eq, LinearMap.mem_ker] at this
      rw [this, Submodule.mem_bot]
    · right
      have hW'eq : W.comap D.proj.mulVecLin = ⊤ := by
        apply Submodule.map_injective_of_injective hinj
        rw [h, Submodule.map_top, D.range_incl]
      rw [eq_top_iff]
      intro w _
      obtain ⟨u, rfl⟩ := hsurj w
      have : u ∈ W.comap D.proj.mulVecLin := by rw [hW'eq]; trivial
      exact this
  · -- every weight is below `nu`
    apply hmax
    intro h0
    apply hmu
    rw [hquot, eq_bot_iff]
    rintro _ ⟨u, hu, rfl⟩
    have hmem : D.incl.mulVecLin u ∈ p.representationWeightSpace ρ mu ⊓
        p.highestGenerated ρ nu := by
      rw [← hsub]
      exact ⟨u, hu, rfl⟩
    rw [h0, bot_inf_eq, Submodule.mem_bot] at hmem
    have hu0 : u = 0 := hinj (hmem.trans (map_zero _).symm)
    rw [hu0, map_zero]
    exact Submodule.zero_mem _

end Langlands.GroupScheme.SplitPinning
