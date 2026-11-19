import Langlands.GroupScheme.Reductive.SplitLeviIsotypicWeights
import Langlands.GroupScheme.Reductive.TitsMaximalWeight
import Langlands.GroupScheme.Reductive.TitsAlgebraTransport
import Langlands.GroupScheme.Reductive.TitsSubquotient
import Langlands.Algebra.GaloisTwistedFlags
import Langlands.Algebra.GaloisTwistedCorner
import Langlands.GroupScheme.SimplyConnected.TrivialStarInnerTwist
import Langlands.GroupScheme.Reductive.TitsKernelStarRestriction
import Langlands.GroupScheme.Reductive.TitsObstructionSimplyConnected
import Langlands.GroupScheme.SimplyConnected.TypeEAnisotropicKernelModel

/-! # Tits obstructions of a group and of the derived group of a split-torus centralizer -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

open MatrixRepresentation Langlands.Algebra.GaloisTwistedMatrix

namespace GaloisPinningData.SplitTorusDatum

variable {F K : Type u} [Field F] [Field K] [Algebra F K]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {n : Type} [Fintype n] [DecidableEq n] {d : GaloisPinningData F K G}

/-- The Galois action on characters of the base change of a split torus is trivial. -/
theorem galoisRepresentation_splitCharacter (s : d.SplitTorusDatum) (σ : K ≃ₐ[F] K)
    (χ : rationalCharacters ((GroupScheme.baseChange (algebraBaseMap F K)).obj
      s.splitTorus.toGrp)) :
    rationalCharacters.galoisRepresentation F K s.splitTorus.toGrp σ χ = χ :=
  TrivialStarInnerTwist.galoisRepresentation_of_isSplitTorus s.splitTorus s.isSplitTorus σ χ

/-- Every isotypic subspace for the split torus is stable under the twisted Galois action
`u ↦ σ⁻¹(P σ u)` attached to Galois intertwiners `P σ : ρ → ρ^σ`. -/
theorem isTwistedStable_isotypicSubspace (s : d.SplitTorusDatum)
    {ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap F K)).obj G) n}
    (P : (K ≃ₐ[F] K) → Matrix n n K) (hP : ∀ σ, ρ.Intertwines (galoisTwist σ ρ) (P σ))
    (μ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap F K)).obj d.torus)) :
    IsTwistedStable P (s.isotypicSubspace ρ μ) := by
  have := s.isAffineHom_baseChange
  intro σ u hu
  have h1 : P σ *ᵥ u ∈ ((galoisTwist σ ρ).restrict ((GroupScheme.baseChange
      (algebraBaseMap F K)).map s.splitInclusion)).characterSpace (s.splitCharacter μ) :=
    Intertwines.mem_characterSpace ((hP σ).restrict _) hu
  have h2 := conjugate_mem_characterSpace_restrict_galoisTwist σ⁻¹ (galoisTwist σ ρ)
    s.splitInclusion (s.splitCharacter μ) h1
  rw [characterSpace_restrict_eq_of_universalMatrix_eq _ (universalMatrix_galoisTwist_inv σ ρ),
    s.galoisRepresentation_splitCharacter] at h2
  exact h2

end GaloisPinningData.SplitTorusDatum

namespace MatrixRepresentation

variable {F K : Type u} [Field F] [Field K] [Algebra F K]
  {D : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom D.X.hom]
  {n : Type} [Fintype n] [DecidableEq n] {m : ℕ}

local instance splitLeviTitsBaseChangeAffine :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap F K)).obj D).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd D.X.hom (algebraBaseMap F K))
  infer_instance

omit [DecidableEq n] in
theorem map_mul_rect_left {A : Type*} [CommRing A] [Algebra K A] {p r : Type*}
    (C : Matrix p n K) (M : Matrix n r A) (ℓ : A →ₗ[K] K) :
    (C.map (algebraMap K A) * M).map ℓ = C * M.map ℓ := by
  ext i j
  have hs (c : K) (a : A) : ℓ (algebraMap K A c * a) = c * ℓ a := by
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  simp only [Matrix.map_apply, Matrix.mul_apply, map_sum, hs]

omit [DecidableEq n] in
theorem map_mul_rect_right {A : Type*} [CommRing A] [Algebra K A] {p r : Type*}
    (M : Matrix p n A) (C : Matrix n r K) (ℓ : A →ₗ[K] K) :
    (M * C.map (algebraMap K A)).map ℓ = M.map ℓ * C := by
  ext i j
  have hs (a : A) (c : K) : ℓ (a * algebraMap K A c) = ℓ a * c := by
    rw [mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  simp only [Matrix.map_apply, Matrix.mul_apply, map_sum, hs]

variable (ρ : MatrixRepresentation ((GroupScheme.baseChange (algebraBaseMap F K)).obj D) n)
  (B : Matrix n (Fin m) K) (C : Matrix (Fin m) n K) (hCB : C * B = 1)
  (hst : ρ.IsStableCoordinates B C)

/-- The universal matrix of a coordinate subrepresentation is the compression of the ambient
universal matrix. -/
theorem universalMatrix_restrictCoordinates :
    universalMatrix (restrictCoordinates ρ B C hCB hst) =
      C.map (algebraMap K (K ⊗[F] CharacterUnits.Coord D)) * universalMatrix ρ *
        B.map (algebraMap K (K ⊗[F] CharacterUnits.Coord D)) :=
  restrictCoordinates_affineMatrix ρ B C hCB hst _ _

/-- The coefficient matrices of a coordinate subrepresentation are compressions of the ambient
coefficient matrices. -/
theorem coefficientMatrix_restrictCoordinates (φ : CharacterUnits.Coord D →ₗ[F] F) :
    coefficientMatrix (restrictCoordinates ρ B C hCB hst) φ = C * coefficientMatrix ρ φ * B := by
  rw [coefficientMatrix, universalMatrix_restrictCoordinates, map_mul_rect_right,
    map_mul_rect_left]
  rfl

variable {ρ B C hCB hst}

omit [DecidableEq n] in
theorem mul_col_eq_mulVec (X : Matrix n n K) (j : Fin m) :
    (fun r => (X * B) r j) = X *ᵥ (fun r => B r j) := rfl

/-- If `f` fixes a stable subspace `V` containing the columns of `B`, the coefficient matrices
of the coordinate subrepresentation are the compressions along `C * f` and `B`. -/
theorem coefficientMatrix_restrictCoordinates_eq {V : Submodule K (n → K)}
    (hV : ρ.IsStableSubspace V) (hcols : ∀ j, (fun r => B r j) ∈ V)
    {f : Matrix n n K} (hfV : ∀ v ∈ V, f *ᵥ v = v) (φ : CharacterUnits.Coord D →ₗ[F] F) :
    coefficientMatrix (restrictCoordinates ρ B C hCB hst) φ =
      (C * f) * coefficientMatrix ρ φ * B := by
  rw [coefficientMatrix_restrictCoordinates]
  have hfix : f * (coefficientMatrix ρ φ * B) = coefficientMatrix ρ φ * B := by
    ext i j
    have hcol : (fun r => (coefficientMatrix ρ φ * B) r j) ∈ V := by
      rw [mul_col_eq_mulVec]
      exact coefficientMatrix_mulVec_mem hV φ (hcols j)
    exact congrFun (hfV _ hcol) i
  calc C * coefficientMatrix ρ φ * B = C * (f * (coefficientMatrix ρ φ * B)) := by
        rw [hfix, Matrix.mul_assoc]
    _ = C * f * coefficientMatrix ρ φ * B := by simp only [Matrix.mul_assoc]

/-- The Tits algebra of the coordinate subrepresentation lies in the compression of any algebra
containing the Tits algebra of the ambient representation. -/
theorem titsAlgebra_restrictCoordinates_le_compressed {Bk : Subalgebra F (Matrix n n K)}
    (hρB : titsAlgebra ρ ≤ Bk) {V : Submodule K (n → K)}
    (hV : ρ.IsStableSubspace V) (hcols : ∀ j, (fun r => B r j) ∈ V)
    {f : Matrix n n K} (hfV : ∀ v ∈ V, f *ᵥ v = v) (hFE : (C * f) * B = 1)
    (hEF : B * (C * f) ∈ Bk) :
    titsAlgebra (restrictCoordinates ρ B C hCB hst) ≤ compressed Bk (C * f) B hFE hEF := by
  rw [titsAlgebra, Algebra.adjoin_le_iff]
  rintro _ ⟨φ, rfl⟩
  exact ⟨coefficientMatrix ρ φ, hρB (Algebra.subset_adjoin ⟨φ, rfl⟩),
    (coefficientMatrix_restrictCoordinates_eq hV hcols hfV φ).symm⟩

/-- Compressed Galois intertwiners intertwine the coordinate subrepresentation with its Galois
twists, when the idempotent `f` is twisted-fixed, fixes the columns of `B`, and has image in
the span of `B`. -/
theorem intertwines_galoisTwist_restrictCoordinates (σ : K ≃ₐ[F] K) {P : Matrix n n K}
    (hP : ρ.Intertwines (galoisTwist σ ρ) P) {f : Matrix n n K}
    (hfP : P * f = f.map σ * P) (hfB : f * B = B) (hBCf : B * C * f = f) :
    (restrictCoordinates ρ B C hCB hst).Intertwines
      (galoisTwist σ (restrictCoordinates ρ B C hCB hst)) ((C * f).map σ * P * B) := by
  have hP' := (intertwines_iff_universalMatrix _ _ _).mp hP
  rw [universalMatrix_galoisTwist] at hP'
  have hUB : B.map (algebraMap K (K ⊗[F] CharacterUnits.Coord D)) * (C.map (algebraMap K (K ⊗[F] CharacterUnits.Coord D)) * ((universalMatrix ρ) * B.map (algebraMap K (K ⊗[F] CharacterUnits.Coord D)))) = (universalMatrix ρ) * B.map (algebraMap K (K ⊗[F] CharacterUnits.Coord D)) := by
    have h := (intertwines_iff_universalMatrix _ _ _).mp
      (intertwines_restrictCoordinates ρ B C hCB hst)
    rw [universalMatrix_restrictCoordinates] at h
    simpa only [Matrix.mul_assoc] using h
  have hτι : ∀ {p q : Type} (X : Matrix p q K), (X.map (algebraMap K (K ⊗[F] CharacterUnits.Coord D))).map (galoisTensor (CharacterUnits.Coord D) σ) = (X.map σ).map (algebraMap K (K ⊗[F] CharacterUnits.Coord D)) := by
    intro p q X
    ext i j
    rfl
  have hfP' : ∀ {q : Type} (Y : Matrix n q (K ⊗[F] CharacterUnits.Coord D)),
      P.map (algebraMap K (K ⊗[F] CharacterUnits.Coord D)) * (f.map (algebraMap K (K ⊗[F] CharacterUnits.Coord D)) * Y) = (f.map σ).map (algebraMap K (K ⊗[F] CharacterUnits.Coord D)) * (P.map (algebraMap K (K ⊗[F] CharacterUnits.Coord D)) * Y) := by
    intro q Y
    rw [← Matrix.mul_assoc, ← Matrix.map_mul, hfP, Matrix.map_mul, Matrix.mul_assoc]
  have hfB' : f.map (algebraMap K (K ⊗[F] CharacterUnits.Coord D)) * B.map (algebraMap K (K ⊗[F] CharacterUnits.Coord D)) = B.map (algebraMap K (K ⊗[F] CharacterUnits.Coord D)) := by rw [← Matrix.map_mul, hfB]
  have hfB'' : ∀ {q : Type} (Y : Matrix (Fin m) q (K ⊗[F] CharacterUnits.Coord D)),
      f.map (algebraMap K (K ⊗[F] CharacterUnits.Coord D)) * (B.map (algebraMap K (K ⊗[F] CharacterUnits.Coord D)) * Y) = B.map (algebraMap K (K ⊗[F] CharacterUnits.Coord D)) * Y := by
    intro q Y
    rw [← Matrix.mul_assoc, hfB']
  have hBCf' : ∀ {q : Type} (Y : Matrix n q (K ⊗[F] CharacterUnits.Coord D)),
      (B.map σ).map (algebraMap K (K ⊗[F] CharacterUnits.Coord D)) * ((C.map σ).map (algebraMap K (K ⊗[F] CharacterUnits.Coord D)) * ((f.map σ).map (algebraMap K (K ⊗[F] CharacterUnits.Coord D)) * Y)) =
        (f.map σ).map (algebraMap K (K ⊗[F] CharacterUnits.Coord D)) * Y := by
    intro q Y
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.map_mul, ← Matrix.map_mul,
      ← Matrix.map_mul, ← Matrix.map_mul, hBCf]
  rw [intertwines_iff_universalMatrix, universalMatrix_galoisTwist,
    universalMatrix_restrictCoordinates]
  simp only [Matrix.map_mul, Matrix.mul_assoc, hτι]
  rw [hUB, ← hfP', ← hUB, hfB'', hUB, ← Matrix.mul_assoc (P.map (algebraMap K (K ⊗[F] CharacterUnits.Coord D))), hP', Matrix.mul_assoc,
    hBCf', ← hfP', hfB']

end MatrixRepresentation

namespace GaloisPinningData.LeviComparison

open Langlands.Brauer

variable {F K : Type u} [Field F] [Field K] [Algebra F K] [IsGalois F K]
  {G D : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffineHom D.X.hom]
  [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType D.X.hom]
  {d : GaloisPinningData F K G} {s : d.SplitTorusDatum} {ι : D ⟶ G}
  {e : GaloisPinningData F K D}

local instance splitLeviTitsBaseChangeAffineG :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap F K)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap F K))
  infer_instance

omit [IsGalois F K] in
/-- Pairing a restricted character with a simple coroot of `D` is the pairing with the
corresponding simple coroot of `G`. -/
theorem pairing_weightRestriction (L : d.LeviComparison s ι e)
    (x : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap F K)).obj d.torus))
    (b : e.base.support) :
    e.rootDatum.toLinearMap (L.weightRestriction x) (e.rootDatum.coroot b) =
      d.rootDatum.toLinearMap x (d.rootDatum.coroot (L.vertexEquiv b).val.val) := by
  change e.rootDatum.toLinearMap
      ((CommGroupScheme.baseChange (algebraBaseMap F K)).map L.kernelTorusMap ≫ x)
      (e.rootDatum.coroot b) = _
  rw [e.isRootDatum.1, d.isRootDatum.1, latticePairing_precomp, L.coroot_eq]

omit [IsGalois F K] in
/-- Restriction preserves dominance. -/
theorem isDominantWeight_weightRestriction (L : d.LeviComparison s ι e)
    {x : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap F K)).obj d.torus)}
    (hx : d.toSplitPinning.IsDominantWeight x) :
    e.toSplitPinning.IsDominantWeight (L.weightRestriction x) := fun b => by
  have := L.pairing_weightRestriction x b
  change 0 ≤ e.rootDatum.toLinearMap (L.weightRestriction x) (e.rootDatum.coroot b.val)
  rw [this]
  exact hx (L.vertexEquiv b).val

omit [IsGalois F K] [IsAffineHom D.X.hom] [LocallyOfFiniteType D.X.hom] in
/-- Pairing a star-transported character with a simple coroot is the pairing of the original
character with the coroot at the vertex moved by the inverse element. -/
theorem _root_.Langlands.GroupScheme.GaloisPinningData.pairing_starAction_weight_coroot
    (d : GaloisPinningData F K G) (σ : K ≃ₐ[F] K)
    (x : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap F K)).obj d.torus))
    (a : d.base.support) :
    d.rootDatum.toLinearMap ((d.starAction σ).val.weightEquiv x) (d.rootDatum.coroot a.val) =
      d.rootDatum.toLinearMap x (d.rootDatum.coroot (d.vertexStar σ⁻¹ a).val) := by
  have hs : (d.starAction σ).val.indexEquiv.symm a.val = (d.vertexStar σ⁻¹ a).val := by
    change _ = (d.starAction σ⁻¹).val.indexEquiv a.val
    rw [map_inv]
    rfl
  have h := TitsIndexData.aut_pairing_weightEquiv_coroot d.toSplitPinning.rootDatum
    (d.starAction σ).val x a.val
  rw [hs] at h
  exact h

omit [IsGalois F K] in
/-- Restriction intertwines the full star actions, when the simple coroots of `D` span its
cocharacter lattice. -/
theorem weightRestriction_starAction (L : d.LeviComparison s ι e)
    (hspan' : e.toSplitPinning.rootDatum.corootSpan ℤ = ⊤) (σ : K ≃ₐ[F] K)
    (x : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap F K)).obj d.torus)) :
    L.weightRestriction ((d.starAction σ).val.weightEquiv x) =
      (e.starAction σ).val.weightEquiv (L.weightRestriction x) := by
  apply IntegralWeylVector.eq_of_pairing_simple_eq e.toSplitPinning.rootDatum e.base hspan'
  intro b
  have h1 := L.pairing_weightRestriction ((d.starAction σ).val.weightEquiv x) b
  have h2 := d.pairing_starAction_weight_coroot σ x (L.vertexEquiv b).val
  have h3 := e.pairing_starAction_weight_coroot σ (L.weightRestriction x) b
  have h4 := L.pairing_weightRestriction x (e.vertexStar σ⁻¹ b)
  rw [L.star_eq] at h4
  exact h1.trans (h2.trans (h4.symm.trans h3.symm))

omit [IsGalois F K] in
/-- Restriction carries star-fixed weights of `G` to star-fixed weights of `D`. -/
theorem isStarFixedWeight_weightRestriction (L : d.LeviComparison s ι e)
    (hspan' : e.toSplitPinning.rootDatum.corootSpan ℤ = ⊤)
    {x : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap F K)).obj d.torus)}
    (hx : d.IsStarFixedWeight x) : e.IsStarFixedWeight (L.weightRestriction x) := fun σ => by
  rw [← L.weightRestriction_starAction hspan', hx σ]

/-- The comparison of Tits obstructions for a dominant star-fixed weight: the Tits class of
`G` at `λ` equals the Tits class of `D` at the restriction of `λ` to the torus of `D`. -/
theorem titsObstructionValue_eq_of_isDominantWeight (L : d.LeviComparison s ι e)
    (hspan : d.toSplitPinning.rootDatum.corootSpan ℤ = ⊤)
    (hspan' : e.toSplitPinning.rootDatum.corootSpan ℤ = ⊤)
    {lam : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap F K)).obj d.torus)}
    (hdom : d.toSplitPinning.IsDominantWeight lam) (hfix : d.IsStarFixedWeight lam)
    (hfix' : e.IsStarFixedWeight (L.weightRestriction lam)) :
    d.titsObstructionValue hspan lam hfix =
      e.titsObstructionValue hspan' (L.weightRestriction lam) hfix' := by
  classical
  obtain ⟨N, ρ, hρ⟩ := (splitHighestWeightClassification K _ d.toSplitPinning).1 lam hdom
  have := d.nonempty_of_isHighestWeight hρ
  choose P hPi hPu using fun σ => d.exists_intertwiner_galoisTwist hρ hfix σ
  have hscalar := SplitPinning.IsHighestWeight.intertwiner_eq_scalar d.toSplitPinning hρ
  have hB : titsAlgebra ρ ≤ twistedFixed P := titsAlgebra_le_twistedFixed P hPi
  have hBs := span_titsAlgebra_eq_top ρ hρ.1 hscalar
  -- the obstruction of `G`
  have hG : d.titsObstructionValue hspan lam hfix =
      classOf (toCSA P hPu (titsAlgebra ρ) hB hBs) := by
    refine d.titsObstructionValue_of_maximal hspan P hPi hPu _ hB hBs le_rfl hfix hρ.2.2.1 ?_
    intro (mu : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap F K)).obj d.torus))
      hmu hle
    have h1 := hρ.2.2.2 mu hmu
    have h2 : -(lam - mu) ∈ d.toSplitPinning.positiveRootMonoid := by rwa [neg_sub]
    have := d.toSplitPinning.eq_zero_of_mem_positiveRootMonoid_of_neg_mem h1 h2
    rw [sub_eq_zero] at this
    exact this.symm
  -- the restricted representation
  set ρ' := ρ.restrict ((GroupScheme.baseChange (algebraBaseMap F K)).map ι) with hρ'
  have hP' : ∀ σ, ρ'.Intertwines (galoisTwist σ ρ') (P σ) := fun σ =>
    intertwines_restrict_galoisTwist σ (hPi σ) ι
  have hρ'B : titsAlgebra ρ' ≤ titsAlgebra ρ := by
    rw [titsAlgebra_eq_twistedFixed ρ hρ.1 hscalar P hPu hPi]
    exact titsAlgebra_le_twistedFixed P hP'
  -- the isotypic subspace and a rational idempotent onto it
  have hVst := L.isStableSubspace_isotypicSubspace ρ lam
  have hVtw := s.isTwistedStable_isotypicSubspace P hPi lam
  have hbot : IsTwistedStable P (⊥ : Submodule K (Fin N → K)) := by
    intro σ u hu
    rw [Submodule.mem_bot] at hu ⊢
    subst hu
    funext i
    simp
  obtain ⟨f, hfB, -, hfX, -, hfid⟩ :=
    exists_adapted_idempotent P hPu (titsAlgebra ρ) hB hBs bot_le hVtw hbot
  have hfV : ∀ v ∈ s.isotypicSubspace ρ lam, f *ᵥ v = v := fun v hv => by
    have := hfid v hv
    rwa [Submodule.mem_bot, sub_eq_zero] at this
  obtain ⟨m, Bc, Cc, hCB, hcols, hproj, hst⟩ := L.exists_isotypicCoordinates ρ lam
  have hfBc : f * Bc = Bc := by
    ext i j
    exact congrFun (hfV _ (hcols j)) i
  have hBCf : Bc * Cc * f = f := by
    ext i j
    have hcol : (fun r => f r j) ∈ s.isotypicSubspace ρ lam := by
      have := hfX (Pi.single j 1)
      convert this using 1
      funext r
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    have := congrFun (hproj _ hcol) i
    rw [← this]
    rfl
  have hFE : (Cc * f) * Bc = 1 := by rw [Matrix.mul_assoc, hfBc, hCB]
  have hEF : Bc * (Cc * f) ∈ titsAlgebra ρ := by rw [← Matrix.mul_assoc, hBCf]; exact hfB
  -- the coordinate representation of `D`
  have hmult := L.finrank_representationWeightSpace_isotypicCoordinates hρ Bc Cc hCB hcols
    hproj hst
  have : Nonempty (Fin m) := by
    by_contra hm
    rw [not_nonempty_iff] at hm
    have hle := Submodule.finrank_le (e.toSplitPinning.representationWeightSpace
      (restrictCoordinates ρ' Bc Cc hCB hst) (L.weightRestriction lam))
    rw [hmult, Module.finrank_fintype_fun_eq_card, Fintype.card_eq_zero] at hle
    exact absurd hle (by norm_num)
  have hP0i : ∀ σ, (restrictCoordinates ρ' Bc Cc hCB hst).Intertwines
      (galoisTwist σ (restrictCoordinates ρ' Bc Cc hCB hst)) ((Cc * f).map σ * P σ * Bc) :=
    fun σ => intertwines_galoisTwist_restrictCoordinates σ (hP' σ) (hB hfB σ) hfBc hBCf
  have hρ0B := titsAlgebra_restrictCoordinates_le_compressed (hCB := hCB) (hst := hst) hρ'B hVst hcols hfV
    hFE hEF
  have hH := e.titsObstructionValue_of_maximal hspan' _ hP0i
    (isUnit_compressed_twist hB hPu (Cc * f) Bc hFE hEF) _
    (compressed_le_twistedFixed hB (Cc * f) Bc hFE hEF)
    (span_compressed hBs (Cc * f) Bc hFE hEF) hρ0B hfix' hmult
    (fun mu h1 h2 => L.eq_of_representationWeightSpace_isotypicCoordinates_ne_bot hρ Bc Cc hCB
      hcols hproj hst h1 h2)
  rw [hG, hH]
  exact ((classOf_eq_iff _ _).mpr
    (isBrauerEquivalent_toCSA_compressed P hPu (titsAlgebra ρ) hB hBs (Cc * f) Bc hFE hEF)).symm

/-- The comparison of Tits obstructions: for every star-fixed weight `λ` of `G`, the Tits
obstruction of `G` at `λ` is the Tits obstruction of `D` at the restriction of `λ`. -/
theorem titsObstructionValue_eq (L : d.LeviComparison s ι e)
    (hspan : d.toSplitPinning.rootDatum.corootSpan ℤ = ⊤)
    (hspan' : e.toSplitPinning.rootDatum.corootSpan ℤ = ⊤)
    {lam : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap F K)).obj d.torus)}
    (hfix : d.IsStarFixedWeight lam) :
    d.titsObstructionValue hspan lam hfix =
      e.titsObstructionValue hspan' (L.weightRestriction lam)
        (L.isStarFixedWeight_weightRestriction hspan' hfix) := by
  set a : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap F K)).obj d.torus) :=
    d.dominantPart hspan lam with ha_def
  have ha := d.isDominantWeight_dominantPart hspan lam
  have hb := d.isDominantWeight_dominantPart_sub hspan lam
  have hfa := d.isStarFixedWeight_dominantPart hspan hfix
  have hfb := d.isStarFixedWeight_sub hfa hfix
  have hG := d.titsObstructionValue_eq_sub hspan hfix ha hb hfa hfb (sub_sub_cancel a lam).symm
  have hH := e.titsObstructionValue_eq_sub hspan' (L.isStarFixedWeight_weightRestriction hspan' hfix)
    (L.isDominantWeight_weightRestriction ha) (L.isDominantWeight_weightRestriction hb)
    (L.isStarFixedWeight_weightRestriction hspan' hfa)
    (L.isStarFixedWeight_weightRestriction hspan' hfb)
    ((congrArg L.weightRestriction (sub_sub_cancel a lam).symm).trans
      (map_sub L.weightRestriction a (a - lam)))
  rw [hG, hH, ← d.titsObstructionValue_of_isDominantWeight hspan hfa ha,
    ← d.titsObstructionValue_of_isDominantWeight hspan hfb hb,
    ← e.titsObstructionValue_of_isDominantWeight hspan' _ (L.isDominantWeight_weightRestriction ha),
    ← e.titsObstructionValue_of_isDominantWeight hspan' _ (L.isDominantWeight_weightRestriction hb),
    L.titsObstructionValue_eq_of_isDominantWeight hspan hspan' ha hfa,
    L.titsObstructionValue_eq_of_isDominantWeight hspan hspan' hb hfb]

omit [IsGalois F K] in
/-- Restriction as an additive map between the star-fixed weights of `G` and of `D`. -/
def starFixedRestriction (L : d.LeviComparison s ι e)
    (hspan' : e.toSplitPinning.rootDatum.corootSpan ℤ = ⊤) :
    d.starFixedWeights →+ e.starFixedWeights where
  toFun lam := ⟨L.weightRestriction lam.1, (e.mem_starFixedWeights _).mpr
    (L.isStarFixedWeight_weightRestriction hspan'
      ((d.mem_starFixedWeights _).mp lam.2))⟩
  map_zero' := Subtype.ext (map_zero L.weightRestriction)
  map_add' x y := Subtype.ext (map_add L.weightRestriction x.1 y.1)

omit [IsGalois F K] in
@[simp] theorem starFixedRestriction_apply (L : d.LeviComparison s ι e)
    (hspan' : e.toSplitPinning.rootDatum.corootSpan ℤ = ⊤) (lam : d.starFixedWeights) :
    (L.starFixedRestriction hspan' lam : characterLattice e.toSplitPinning.torus) =
      L.weightRestriction lam.1 := rfl

/-- For simply connected `G` and `D`, the actual Tits obstruction of `G` is the actual Tits
obstruction of `D` composed with restriction of star-fixed weights. -/
theorem titsObstruction_comp_starFixedRestriction (L : d.LeviComparison s ι e)
    (hG : IsSimplyConnected G) (hD : IsSimplyConnected D) :
    (e.titsObstruction hD).comp
        (L.starFixedRestriction (e.corootSpan_eq_top_of_simplyConnected hD)) =
      d.titsObstruction hG := by
  ext lam
  rw [AddMonoidHom.comp_apply, titsObstruction_apply, titsObstruction_apply]
  exact (L.titsObstructionValue_eq (d.corootSpan_eq_top_of_simplyConnected hG)
    (e.corootSpan_eq_top_of_simplyConnected hD) _).symm

end GaloisPinningData.LeviComparison

namespace TitsIndexData.AnisotropicKernelIndex

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] {d : TitsIndexData G}

/-- Clause 2 of the comparison with the anisotropic kernel: for simply connected `G` and the
actual anisotropic kernel `p.kernel` (the derived subgroup of the actual centralizer of the
maximal split torus), the actual Tits obstruction of `G` at every star-fixed weight `λ` is the
actual Tits obstruction of the kernel at the restriction of `λ` to its torus. -/
theorem titsObstruction_eq (p : d.AnisotropicKernelIndex) (hG : IsSimplyConnected G)
    (lam : d.pinning.starFixedWeights) :
    d.pinning.titsObstruction hG lam =
      p.index.pinning.titsObstruction (p.isSimplyConnected hG)
        (p.leviComparison.starFixedRestriction
          (p.index.pinning.corootSpan_eq_top_of_simplyConnected (p.isSimplyConnected hG)) lam) :=
  (DFunLike.congr_fun (p.leviComparison.titsObstruction_comp_starFixedRestriction hG
    (p.isSimplyConnected hG)) lam).symm

end TitsIndexData.AnisotropicKernelIndex

end Langlands.GroupScheme
