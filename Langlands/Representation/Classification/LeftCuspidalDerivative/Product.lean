import Langlands.Representation.Classification.LeftCuspidalDerivative.FirstBlock
import Langlands.Representation.Classification.LeftCuspidalDerivative.Segments
import Langlands.Representation.Geometric.GeometricLemmaProof
import Langlands.Representation.CuspidalSupport.JacquetSubquotientProof
import Langlands.Representation.Filtration.GroupRestriction
import Langlands.Representation.Derivative.ProductDerivativesFiniteLength
import Langlands.Representation.Tensor.ExternalSubquotient
import Langlands.Representation.Smooth.IrreducibleRealization

/-!
# Products of left reduced representations (clause 2)

If `Y₁` and `Y₂` are finite-length and left `A`-reduced, so is `Y₁ × Y₂`. An irreducible
subquotient `Z` of `Y₁ × Y₂` embedding into `A × σ` makes `A` a quotient of the first block of
the Jacquet module of `Z`, hence a subquotient of the first block of one geometric piece of
`r(Y₁ × Y₂)`; the per-piece statement `BinaryGeometricPieceConstituents` then makes `A` a
first-block constituent of `Y₁` or `Y₂` (excluded by the first-block criterion) or a
subquotient of a proper normalized product (excluded by supercuspidality).
-/

noncomputable section

open CategoryTheory
open scoped TensorProduct

namespace Langlands.Classification.LeftCuspidalDerivative

universe uF uV uG uX uA uW uC vC

section FirstBlockQuotient

variable {H : Fin 2 → Type uG} [∀ i, Group (H i)] {U : Type uX} [AddCommGroup U] [Module ℂ U]
  {W : Fin 2 → Type uA} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

/-- A nonzero intertwiner from `ρ` into a two-factor external tensor whose first factor is
irreducible exhibits that first factor as a quotient of the restriction of `ρ` to the first
factor group. -/
theorem isSubquotient_firstBlock_of_ne_zero (ρ : Representation ℂ (∀ i, H i) U)
    (τ : ∀ i, Representation ℂ (H i) (W i)) (hτ : (τ 0).IsIrreducible)
    (f : ρ.IntertwiningMap (FiniteTensor.external τ)) (hf : f ≠ 0) :
    WeylBranchPieces.IsSubquotient (ρ.comp (MonoidHom.mulSingle H 0)) (τ 0) := by
  have := hτ
  obtain ⟨v, hv⟩ : ∃ v, f v ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (Representation.IntertwiningMap.ext (LinearMap.ext h))
  obtain ⟨φ, hφ⟩ := exists_dual_rid_lTensor_ne_zero
    (w := FiniteTensor.headTailLinearEquiv (r := 1) ℂ W (f v))
    (fun h0 => hv ((FiniteTensor.headTailLinearEquiv (r := 1) ℂ W).injective
      (h0.trans (map_zero _).symm)))
  let F : Representation.IntertwiningMap (ρ.comp (MonoidHom.mulSingle H 0))
      ((FiniteTensor.external τ).comp (MonoidHom.mulSingle H 0)) :=
    { toLinearMap := f.toLinearMap
      isIntertwining' := fun h => f.isIntertwining' _ }
  let g := (firstSlotContraction τ φ).comp F
  have hg : g ≠ 0 := fun h0 => hφ (congrArg (fun g : Representation.IntertwiningMap _ _ => g v) h0)
  exact WeylBranchPieces.IsSubquotient.of_surjective g
    ((Representation.IsIrreducible.surjective_or_eq_zero g).resolve_right hg)

end FirstBlockQuotient

section GluedRestriction

variable {G : Type uG} [Group G] {H : Type uA} [Group H] {X : Type uX}
  [AddCommGroup X] [Module ℂ X] {C : Type uC} [Category.{vC} C]

/-- An irreducible subquotient of the restriction of a glued representation is a
subquotient of the restriction of one piece. -/
theorem exists_isSubquotient_piece_comp {F : C ⥤ Rep.{uV} ℂ G} {n : ℕ}
    {pieces : Fin n → C ⥤ Rep.{uV} ℂ G} (h : IsGluedFrom F pieces) (φ : H →* G) (Y : C)
    {ρ : Representation ℂ H X} (hirr : ρ.IsIrreducible)
    (hρ : WeylBranchPieces.IsSubquotient ((F.obj Y).ρ.comp φ) ρ) :
    ∃ i : Fin n, WeylBranchPieces.IsSubquotient (((pieces i).obj Y).ρ.comp φ) ρ := by
  have := hirr
  obtain ⟨e, s, hs⟩ := h
  obtain ⟨j, hj⟩ := WeylBranchPieces.exists_isSubquotient_graded (s.restrictGroup φ) Y hρ
  obtain ⟨ψ⟩ := hs j
  refine ⟨e j, ?_⟩
  have e₁ := (s.restrictGroupGradedIso φ j).app Y
  have e₂ := (Rep.resFunctor φ).mapIso (ψ.app Y)
  exact (WeylBranchPieces.isSubquotient_of_iso (e₁ ≪≫ e₂).symm).trans hj

end GluedRestriction

section Supercuspidal

open GeneralLinear

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- An admissible representation of `GL_d` having a supercuspidal `A` as a subquotient
contains `A` as a subrepresentation. -/
theorem exists_injective_of_isSubquotient_supercuspidal {d : ℕ} (hd : 0 < d)
    (A : letI := T.topology; GeneralLinear.SupercuspidalRep.{uF, uW} (F := F.Carrier) (n := d))
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear d F.Carrier) V)
    (hρ : letI := T.topology; IsAdmissible ρ)
    (hocc : letI := T.topology; WeylBranchPieces.IsSubquotient ρ A.obj.representation) :
    letI := T.topology; ∃ i : A.obj.representation.IntertwiningMap ρ, Function.Injective i := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let B := CuspidalSupport.LeviAdmissibility.oneBlock d hd
  have hB : B.length = 1 := rfl
  have hsurj : Function.Surjective (B.leviEmbedding F.Carrier) :=
    B.singleBlock_leviEmbedding_surjective hB F.Carrier
  have hAa : IsAdmissible (Rep.of (ρ.comp (B.leviEmbedding F.Carrier))).ρ :=
    isAdmissible_comp_continuousMulEquiv ρ (B.singleBlockLeviEquivContinuous hB F.Carrier) hρ
  have : A.obj.representation.IsIrreducible := A.property.1
  have hDi : Representation.IsIrreducible
      (Rep.of (A.obj.representation.comp (B.leviEmbedding F.Carrier))).ρ :=
    CuspidalSupport.isIrreducible_comp_of_surjective A.obj.representation
      (B.leviEmbedding F.Carrier) hsurj
  have hDc : CuspidalSupport.IsLeviCuspidal B
      (Rep.of (A.obj.representation.comp (B.leviEmbedding F.Carrier))).ρ :=
    (CuspidalSupport.singleBlockCuspidalityClause T d B hB _ A.obj.representation).mpr
      A.property.2
  have hDA : ∃ S : Subrepresentation (Rep.of (ρ.comp (B.leviEmbedding F.Carrier))).ρ,
      ∃ q : S.toRepresentation.IntertwiningMap
        (Rep.of (A.obj.representation.comp (B.leviEmbedding F.Carrier))).ρ,
        Function.Surjective q := by
    obtain ⟨S, q, hq⟩ := hocc
    exact ⟨⟨S.toSubmodule, fun g v hv => S.apply_mem_toSubmodule (B.leviEmbedding F.Carrier g) hv⟩,
      ⟨q.toLinearMap, fun g => q.isIntertwining' (B.leviEmbedding F.Carrier g)⟩, hq⟩
  obtain ⟨⟨i, hi⟩, -⟩ := CuspidalSupport.leviCuspidalConstituent_maps F T B
    (Rep.of (ρ.comp (B.leviEmbedding F.Carrier)))
    (Rep.of (A.obj.representation.comp (B.leviEmbedding F.Carrier))) hAa hDi hDc hDA
  refine ⟨⟨i.toLinearMap, fun g => ?_⟩, hi⟩
  obtain ⟨l, rfl⟩ := hsurj g
  exact i.isIntertwining' l

/-- A supercuspidal representation is not a subquotient of a normalized product of two
finite-length representations of positive ranks. -/
theorem not_isSubquotient_binaryProduct_of_supercuspidal {a₁ a₂ : ℕ} (h₁ : 0 < a₁) (h₂ : 0 < a₂)
    (A : letI := T.topology;
      GeneralLinear.SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := a₁ + a₂))
    (ρ₁ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a₁ F.Carrier))
    (ρ₂ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a₂ F.Carrier))
    (hρ₁ : letI := T.topology; ρ₁.HasFiniteLength) (hρ₂ : letI := T.topology; ρ₂.HasFiniteLength) :
    letI := T.topology
    ¬ WeylBranchPieces.IsSubquotient
      ((T.binaryNormalizedProductFunctor a₁ a₂).obj (ρ₁, ρ₂)).representation
      A.obj.representation := by
  let := T.topology
  intro hocc
  let P := (T.binaryNormalizedProductFunctor a₁ a₂).obj (ρ₁, ρ₂)
  have hP : P.HasFiniteLength :=
    Derivative.ProductDerivativesFiniteLength.binaryProduct_hasFiniteLength T (ρ₁, ρ₂) hρ₁ hρ₂
  have hPa : IsAdmissible P.representation := glFiniteLengthAdmissibility F T (a₁ + a₂) P hP
  obtain ⟨i, hi⟩ := exists_injective_of_isSubquotient_supercuspidal F T (by omega) A
    P.representation hPa hocc
  have : Nontrivial A.obj := by
    have hAirr : A.obj.representation.IsIrreducible := A.property.1
    have : IsSimpleModule (MonoidAlgebra ℂ (GeneralLinear (a₁ + a₂) F.Carrier))
        A.obj.representation.asModule :=
      (Representation.irreducible_iff_isSimpleModule_asModule _).mp hAirr
    exact IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GeneralLinear (a₁ + a₂) F.Carrier))
      A.obj.representation.asModule
  obtain ⟨g, hg⟩ := exists_jacquet_ne_zero_of_isSubrepresentation F T h₁ h₂ rfl A.obj ρ₁ ρ₂
    inferInstance ⟨SmoothRep.ofHom i, hi⟩
  have hsub := subsingleton_jacquet_of_isSupercuspidal F T h₁ h₂ rfl A.obj A.property.2
  apply hg
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  have hv : v = 0 := Subsingleton.elim (α := (T.normalizedJacquetFunctor
    (BlockShape.ofPair a₁ a₂ h₁ h₂ rfl)).obj A.obj) v 0
  rw [hv, map_zero]
  rfl

/-- The same, after an arbitrary rank transport `a₁ + a₂ = a`. -/
theorem not_isSubquotient_castRank_binaryProduct_of_supercuspidal {a₁ a₂ a : ℕ}
    (h₁ : 0 < a₁) (h₂ : 0 < a₂) (h : a₁ + a₂ = a)
    (A : letI := T.topology;
      GeneralLinear.SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := a))
    (ρ₁ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a₁ F.Carrier))
    (ρ₂ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a₂ F.Carrier))
    (hρ₁ : letI := T.topology; ρ₁.HasFiniteLength) (hρ₂ : letI := T.topology; ρ₂.HasFiniteLength) :
    letI := T.topology
    ¬ SmoothRep.IsSubquotient A.obj
      (T.castRank h ((T.binaryNormalizedProductFunctor a₁ a₂).obj (ρ₁, ρ₂))) := by
  let := T.topology
  subst h
  intro hocc
  exact not_isSubquotient_binaryProduct_of_supercuspidal F T h₁ h₂ A ρ₁ ρ₂ hρ₁ hρ₂
    (SmoothRep.isSubquotient_iff_representation.mp hocc)

/-- Rank transport of an actual supercuspidal representation. -/
theorem exists_supercuspidal_castRank {a b : ℕ} (h : a = b)
    (A : letI := T.topology;
      GeneralLinear.SupercuspidalRep.{uF, uW} (F := F.Carrier) (n := a)) :
    letI := T.topology
    ∃ A' : GeneralLinear.SupercuspidalRep.{uF, uW} (F := F.Carrier) (n := b),
      A'.obj = T.castRank h A.obj := by
  subst h
  exact ⟨A, rfl⟩

end Supercuspidal

section RankTransport

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

theorem castRank_castRank {r s t : ℕ} (h₁ : r = s) (h₂ : s = t)
    (X : letI := T.topology; SmoothRep.{0, uF, uW} ℂ (GeneralLinear r F.Carrier)) :
    T.castRank h₂ (T.castRank h₁ X) = T.castRank (h₁.trans h₂) X := by
  subst h₁
  subst h₂
  rfl

theorem isIrreducible_castRank {r s : ℕ} (h : r = s)
    {X : letI := T.topology; SmoothRep.{0, uF, uW} ℂ (GeneralLinear r F.Carrier)}
    (hX : letI := T.topology; X.IsIrreducible) :
    letI := T.topology; (T.castRank h X).IsIrreducible := by
  subst h
  exact hX

theorem isSubquotient_castRank {r s : ℕ} (h : r = s)
    {X Y : letI := T.topology; SmoothRep.{0, uF, uW} ℂ (GeneralLinear r F.Carrier)}
    (hXY : letI := T.topology; SmoothRep.IsSubquotient X Y) :
    letI := T.topology; SmoothRep.IsSubquotient (T.castRank h X) (T.castRank h Y) := by
  subst h
  exact hXY

theorem isSubrepresentation_castRank {r s : ℕ} (h : r = s)
    {X Y : letI := T.topology; SmoothRep.{0, uF, uW} ℂ (GeneralLinear r F.Carrier)}
    (hXY : letI := T.topology; SmoothRep.IsSubrepresentation X Y) :
    letI := T.topology; SmoothRep.IsSubrepresentation (T.castRank h X) (T.castRank h Y) := by
  subst h
  exact hXY

end RankTransport

section Degenerate

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- Irreducible representations are nonzero. -/
theorem nontrivial_of_isIrreducible {Z : SmoothRep.{0, uG, uW} ℂ G} (hZ : Z.IsIrreducible) :
    Nontrivial Z := by
  have : IsSimpleModule (MonoidAlgebra ℂ G) Z.representation.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule _).mp hZ
  exact IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) Z.representation.asModule

/-- A nonzero representation is not a subquotient of a zero representation. -/
theorem not_isSubquotient_of_subsingleton {Z P : SmoothRep.{0, uG, uW} ℂ G}
    [Nontrivial Z] [Subsingleton P] : ¬ SmoothRep.IsSubquotient Z P := by
  intro h
  obtain ⟨U, q, hq⟩ := SmoothRep.isSubquotient_iff_representation.mp h
  obtain ⟨z, hz⟩ := exists_ne (0 : Z)
  obtain ⟨u, rfl⟩ := hq z
  apply hz
  have : u = 0 := Subtype.ext (Subsingleton.elim _ _)
  rw [this, map_zero]

/-- A finite tensor product with a zero factor is zero. -/
theorem subsingleton_piTensorProduct {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)] (i : ι)
    [Subsingleton (V i)] : Subsingleton (PiTensorProduct ℂ V) := by
  refine subsingleton_of_forall_eq 0 fun x => ?_
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    rw [(PiTensorProduct.tprod ℂ).map_coord_zero i (Subsingleton.elim _ _), smul_zero]
  | add x y hx hy => rw [hx, hy, add_zero]

end Degenerate

section RankZero

open GeneralLinear

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- For a nonzero `A` of `GL_0`, every `Z` embeds into `A × Z`. -/
theorem isSubrepresentation_rankZero_product {m : ℕ}
    (A : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear 0 F.Carrier))
    [Nontrivial A]
    (Z : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)) :
    letI := T.topology
    SmoothRep.IsSubrepresentation Z
      (T.castRank (Nat.zero_add m) ((T.binaryNormalizedProductFunctor 0 m).obj (A, Z))) := by
  let := T.topology
  let X := (T.binaryNormalizedProductFunctor 0 m).obj (A, Z)
  let E := T.binaryLeftZeroTensorEquiv (a := 0) (b := m) rfl (A, Z)
  let C := T.castRankEquiv (Nat.zero_add m) X
  obtain ⟨a, ha⟩ := exists_ne (0 : A)
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one ℂ ha
  let ι₀ : Z →ₗ[ℂ] A ⊗[ℂ] Z := TensorProduct.mk ℂ A Z a
  have hι₀ : Function.Injective ι₀ := by
    let r : A ⊗[ℂ] Z →ₗ[ℂ] Z := (TensorProduct.lid ℂ Z).toLinearMap ∘ₗ φ.rTensor Z
    have hr : ∀ z : Z, r (ι₀ z) = z := by
      intro z
      simp [r, ι₀, hφ]
    intro z z' hzz'
    rw [← hr z, ← hr z', hzz']
  let ψ := (GeneralLinear.reindex (R := F.Carrier) (finCongr (Nat.zero_add m))).symm.toMonoidHom
  let ι : Z.representation.IntertwiningMap (T.castRank (Nat.zero_add m) X).representation :=
    { toLinearMap := C.toLinearMap ∘ₗ E.symm.toLinearMap ∘ₗ ι₀
      isIntertwining' := fun g => by
        ext z
        have h1 := LinearMap.congr_fun (C.isIntertwining' g) (E.symm (ι₀ z))
        have h2 := LinearMap.congr_fun (E.symm.isIntertwining' (ψ g)) (ι₀ z)
        have hg :
            GeneralLinear.reindex (R := F.Carrier) (finCongr (by omega : 0 + m = m)) (ψ g) = g :=
          MulEquiv.apply_symm_apply _ g
        have h3 : ι₀ (Z.representation g z) =
            BinaryTensor.rankZeroLeft (R := F.Carrier) (a := 0) (b := m) rfl A Z.representation
              (ψ g) (ι₀ z) := by
          change a ⊗ₜ[ℂ] Z.representation g z = a ⊗ₜ[ℂ] Z.representation
            (GeneralLinear.reindex (R := F.Carrier) (finCongr (by omega : 0 + m = m)) (ψ g)) z
          rw [hg]
        change C (E.symm (ι₀ (Z.representation g z))) =
          (T.castRank (Nat.zero_add m) X).representation g (C (E.symm (ι₀ z)))
        rw [h3]
        exact (congrArg C h2).trans h1 }
  refine ⟨SmoothRep.ofHom ι, ?_⟩
  exact C.injective.comp (E.symm.injective.comp hι₀)

/-- For `d = 0`, a finite-length left `A`-reduced representation is zero. -/
theorem subsingleton_of_leftReduced_rankZero
    (A : letI := T.topology; SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := 0))
    {m : ℕ} (Y : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier))
    (hY : letI := T.topology; Y.HasFiniteLength) (hr : LeftReduced F T A Y) : Subsingleton Y := by
  let := T.topology
  by_contra hns
  have : Nontrivial Y := not_subsingleton_iff_nontrivial.mp hns
  obtain ⟨Z, hZ, j, hj⟩ := SegmentHeadSupport.exists_irreducible_subrepresentation hY
  have hZY : SmoothRep.IsSubquotient Z Y :=
    CuspidalProductContragredient.isSubquotient_of_injective_of_surjective j hj (𝟙 Y)
      (fun y => ⟨y, rfl⟩)
  have : Nontrivial A.obj := nontrivial_of_isIrreducible A.property.1
  exact hr Z hZ hZY m (Nat.zero_add m) Z (isSubrepresentation_rankZero_product F T A.obj Z)

end RankZero

section Main

open GeneralLinear Geometric

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The geometric lemma filtration, restricted to the first block: an irreducible subquotient of
the first-block restriction of `r_(d,k) i_(m₁,m₂) X` is a subquotient of the first-block
restriction of one geometric piece. Stated with the first-block embedding and the piece written
exactly as in `BinaryGeometricPieceConstituents`. -/
theorem exists_isSubquotient_geometricPiece_firstBlock
    {d k m₁ m₂ : ℕ} (hd : 0 < d) (hk : 0 < k) (h₁ : 0 < m₁) (h₂ : 0 < m₂)
    (h : d + k = m₁ + m₂)
    (S : MinimalRepresentatives (BlockShape.ofPair m₁ m₂ h₁ h₂ rfl)
        (BlockShape.ofPair d k hd hk h) → BlockRefinement (BlockShape.ofPair m₁ m₂ h₁ h₂ rfl))
    (R : MinimalRepresentatives (BlockShape.ofPair m₁ m₂ h₁ h₂ rfl)
        (BlockShape.ofPair d k hd hk h) → BlockRefinement (BlockShape.ofPair d k hd hk h))
    (hS : ∀ w, IsIntersectionRefinement (F := F.Carrier) (BlockShape.ofPair m₁ m₂ h₁ h₂ rfl)
        (BlockShape.ofPair d k hd hk h) w.val (S w))
    (hR : ∀ w, IsIntersectionRefinement (F := F.Carrier) (BlockShape.ofPair d k hd hk h)
        (BlockShape.ofPair m₁ m₂ h₁ h₂ rfl) w.val⁻¹ (R w))
    {n : ℕ} (e : Fin n ≃ MinimalRepresentatives (BlockShape.ofPair m₁ m₂ h₁ h₂ rfl)
        (BlockShape.ofPair d k hd hk h))
    (hglue : letI := T.topology;
      IsGluedFrom (jacquetInductionFunctor.{uF, max uF uV} T (BlockShape.ofPair m₁ m₂ h₁ h₂ rfl)
          (BlockShape.ofPair d k hd hk h))
        (fun i => geometricPieceFunctor T (BlockShape.ofPair m₁ m₂ h₁ h₂ rfl)
          (BlockShape.ofPair d k hd hk h) (e i).val (S (e i)) (R (e i)) (hS (e i)).2.1
          (hR (e i)).2.1))
    (X : letI := T.topology;
      SmoothRep.{0, uF, max uF uV} ℂ ((BlockShape.ofPair m₁ m₂ h₁ h₂ rfl).Levi F.Carrier))
    (ρ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear d F.Carrier))
    (hρ : letI := T.topology; ρ.representation.IsIrreducible)
    (hX : letI := T.topology; WeylBranchPieces.IsSubquotient
      (((jacquetInductionFunctor.{uF, max uF uV} T (BlockShape.ofPair m₁ m₂ h₁ h₂ rfl)
        (BlockShape.ofPair d k hd hk h)).obj X).ρ.comp
        (MonoidHom.mulSingle
          (fun i => GeneralLinear ((BlockShape.ofPair d k hd hk h).size i) F.Carrier)
          (0 : Fin 2)))
      ρ.representation) :
    letI := T.topology
    ∃ i : Fin n, WeylBranchPieces.IsSubquotient
      (((geometricPieceFunctor.{uF, max uF uV} T (BlockShape.ofPair m₁ m₂ h₁ h₂ rfl)
          (BlockShape.ofPair d k hd hk h) (e i).val (S (e i)) (R (e i)) (hS (e i)).2.1
          (hR (e i)).2.1).obj X).ρ.comp
        (MonoidHom.mulSingle
          (fun i => GeneralLinear ((BlockShape.ofPair d k hd hk h).size i) F.Carrier)
          (0 : Fin 2)))
      ρ.representation := by
  let := T.topology
  obtain ⟨i, hi⟩ := exists_isSubquotient_piece_comp hglue _ X hρ hX
  exact ⟨i, hi⟩

/-- The positive-rank case of the product clause: for `m₁, m₂, d, k > 0`, an irreducible
subquotient `Z` of `Y₁ × Y₂` embedding into `A × σ` contradicts left reducedness of `Y₁` and
`Y₂`, given the per-piece statement `BinaryGeometricPieceConstituents`. -/
theorem false_of_isSubquotient_binaryProduct_of_pos
    (hPP : BinaryGeometricPieces.BinaryGeometricPieceConstituents.{uF, uV})
    {d k m₁ m₂ : ℕ} (hd : 0 < d) (hk : 0 < k) (h₁ : 0 < m₁) (h₂ : 0 < m₂)
    (h : d + k = m₁ + m₂)
    (A : letI := T.topology; SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := d))
    (Y₁ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m₁ F.Carrier))
    (Y₂ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m₂ F.Carrier))
    (hY₁ : letI := T.topology; Y₁.HasFiniteLength) (hY₂ : letI := T.topology; Y₂.HasFiniteLength)
    (hr₁ : LeftReduced F T A Y₁) (hr₂ : LeftReduced F T A Y₂)
    (Z : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (m₁ + m₂) F.Carrier))
    (hZ : letI := T.topology; Z.IsIrreducible)
    (hZP : letI := T.topology;
      SmoothRep.IsSubquotient Z ((T.binaryNormalizedProductFunctor m₁ m₂).obj (Y₁, Y₂)))
    (σ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear k F.Carrier))
    (hsub : letI := T.topology; SmoothRep.IsSubrepresentation Z
      (T.castRank h ((T.binaryNormalizedProductFunctor d k).obj (A.obj, σ)))) :
    False := by
  let := T.topology
  let H := fun i : Fin 2 => GeneralLinear ((BlockShape.ofPair d k hd hk h).size i) F.Carrier
  let φ : H 0 →* (∀ i, H i) := MonoidHom.mulSingle H 0
  have hZnt : Nontrivial Z := nontrivial_of_isIrreducible hZ
  obtain ⟨g, hg⟩ := exists_jacquet_ne_zero_of_isSubrepresentation F T hd hk h Z A.obj σ hZnt hsub
  have hAirr : A.obj.representation.IsIrreducible := A.property.1
  have h1 : WeylBranchPieces.IsSubquotient
      ((T.normalizedJacquet (BlockShape.ofPair d k hd hk h) Z.representation).comp φ)
      A.obj.representation :=
    isSubquotient_firstBlock_of_ne_zero (H := H) _ _ hAirr g hg
  let P := (T.binaryNormalizedProductFunctor m₁ m₂).obj (Y₁, Y₂)
  have h2 : WeylBranchPieces.IsSubquotient
      ((T.normalizedJacquet (BlockShape.ofPair d k hd hk h) P.representation).comp φ)
      ((T.normalizedJacquet (BlockShape.ofPair d k hd hk h) Z.representation).comp φ) :=
    (SmoothRep.isSubquotient_iff_representation.mp
      (CuspidalSupport.normalizedJacquetSubquotient p F T (m₁ + m₂)
        (BlockShape.ofPair d k hd hk h) P Z hZP)).comp φ
  obtain ⟨e⟩ := SegmentSocleDerivativesProof.nonempty_ofPairProductIso T h₁ h₂ Y₁ Y₂
  let X : SmoothRep.{0, uF, max uF uV} ℂ ((BlockShape.ofPair m₁ m₂ h₁ h₂ rfl).Levi F.Carrier) :=
    FiniteTensor.externalSmoothObject (twoBlockFactors h₁ h₂ Y₁ Y₂)
  have h3 : WeylBranchPieces.IsSubquotient
      (((jacquetInductionFunctor.{uF, max uF uV} T (BlockShape.ofPair m₁ m₂ h₁ h₂ rfl)
        (BlockShape.ofPair d k hd hk h)).obj X).ρ.comp φ)
      ((T.normalizedJacquet (BlockShape.ofPair d k hd hk h) P.representation).comp φ) :=
    (WeylBranchPieces.isSubquotient_of_iso
      (SmoothRep.toRep.mapIso
        ((T.normalizedJacquetFunctor (BlockShape.ofPair d k hd hk h)).mapIso e.symm))).comp φ
  -- Restate with the first-block embedding written as in `BinaryGeometricPieceConstituents`
  -- (index type `Fin (ofPair d k ..).length` instead of `Fin 2`).
  have h4 : WeylBranchPieces.IsSubquotient
      (((jacquetInductionFunctor.{uF, max uF uV} T (BlockShape.ofPair m₁ m₂ h₁ h₂ rfl)
        (BlockShape.ofPair d k hd hk h)).obj
          (FiniteTensor.externalSmoothObject (twoBlockFactors h₁ h₂ Y₁ Y₂))).ρ.comp
        (MonoidHom.mulSingle
          (fun i => GeneralLinear ((BlockShape.ofPair d k hd hk h).size i) F.Carrier)
          (0 : Fin 2)))
      A.obj.representation :=
    h3.trans (h2.trans h1)
  obtain ⟨S, R, hS, hR, mm, eo, hglue⟩ :=
    padicGeometricLemma.{uF, max uF uV} p F T (m₁ + m₂) (by omega)
      (BlockShape.ofPair m₁ m₂ h₁ h₂ rfl) (BlockShape.ofPair d k hd hk h)
  -- The Library's geometric lemma and the lemma above elaborate the same data with different
  -- (abstracted versus inline) proof terms, so every argument is passed by a reducible check.
  obtain ⟨i, hi⟩ := exists_isSubquotient_geometricPiece_firstBlock F T hd hk h₁ h₂ h S R
    (by with_reducible exact hS) (by with_reducible exact hR)
    eo (by with_reducible exact hglue)
    (FiniteTensor.externalSmoothObject (twoBlockFactors h₁ h₂ Y₁ Y₂)) A.obj
    (by with_reducible exact hAirr) (by with_reducible exact h4)
  have key := hPP p F T m₁ m₂ h₁ h₂ d k hd hk h (eo i) (S (eo i)) (R (eo i))
      (by with_reducible exact hS (eo i)) (by with_reducible exact hR (eo i)) Y₁ Y₂ A.obj
      (by with_reducible exact hY₁) (by with_reducible exact hY₂)
      (by with_reducible exact hAirr)
  -- `hi` and the premise of `key` differ only in proof terms (the statement's body has
  -- abstracted auxiliary proofs); the reducible check sees this at once.
  rcases key (by with_reducible exact hi) with ⟨-, hfb⟩ | hfb | hmix
  · exact not_leftReduced_of_isFirstBlockConstituent F T A Y₁ hY₁ hfb hr₁
  · exact not_leftReduced_of_isFirstBlockConstituent F T A Y₂ hY₂ hfb hr₂
  · obtain ⟨a₁, a₂, ha₁, ha₂, ha, ρ₁, ρ₂, hρ₁, hρ₂, -, -, hsq⟩ := hmix
    exact not_isSubquotient_castRank_binaryProduct_of_supercuspidal F T ha₁ ha₂ ha A ρ₁ ρ₂
      (SmoothRep.hasFiniteLength_of_isIrreducible hρ₁)
      (SmoothRep.hasFiniteLength_of_isIrreducible hρ₂) hsq

end Main

section Wrapper

open GeneralLinear

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Left reducedness descends along an exact rank equality: if every irreducible subquotient of
`P` becomes, after the rank transport, a subquotient of a left `A`-reduced `Y`, then `P` is
left `A`-reduced. -/
theorem leftReduced_of_castRank_isSubquotient {d : ℕ}
    (A : letI := T.topology; SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := d))
    {m m' : ℕ} (e : m = m')
    (P : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier))
    (Y : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m' F.Carrier))
    (hPY : letI := T.topology; ∀ Z : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier),
      Z.IsIrreducible → SmoothRep.IsSubquotient Z P → SmoothRep.IsSubquotient (T.castRank e Z) Y)
    (hY : LeftReduced F T A Y) : LeftReduced F T A P := by
  let := T.topology
  subst e
  intro Z hZ hZP k h σ hsub
  exact hY Z hZ (hPY Z hZ hZP) k h σ hsub

/-- For `m₁ = 0`, an irreducible subquotient of `Y₁ × Y₂` is, after the rank transport
`m₁ + m₂ = m₂`, a subquotient of `Y₂`. -/
theorem isSubquotient_of_isSubquotient_binaryProduct_zero_left {m₁ m₂ : ℕ} (ha : m₁ = 0)
    (Y₁ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m₁ F.Carrier))
    (Y₂ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m₂ F.Carrier))
    (Z : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (m₁ + m₂) F.Carrier))
    (hZ : letI := T.topology; Z.IsIrreducible)
    (hZP : letI := T.topology;
      SmoothRep.IsSubquotient Z ((T.binaryNormalizedProductFunctor m₁ m₂).obj (Y₁, Y₂))) :
    letI := T.topology
    SmoothRep.IsSubquotient (T.castRank (by omega : m₁ + m₂ = m₂) Z) Y₂ := by
  let := T.topology
  have e0 : m₁ + m₂ = m₂ := by omega
  let r := GeneralLinear.reindex (R := F.Carrier) (finCongr e0)
  let S := BinaryTensor.secondFactor Y₁ Y₂.representation
  have h1 : WeylBranchPieces.IsSubquotient (S.comp r.toMonoidHom) Z.representation :=
    WeylBranchPieces.IsSubquotient.of_equiv_left (T.binaryLeftZeroTensorEquiv ha (Y₁, Y₂)).symm
      (SmoothRep.isSubquotient_iff_representation.mp hZP)
  have hc : (S.comp r.toMonoidHom).comp r.symm.toMonoidHom = S := by
    ext g v
    simp
  have h2 : WeylBranchPieces.IsSubquotient S (Z.representation.comp r.symm.toMonoidHom) := by
    have := h1.comp r.symm.toMonoidHom
    rwa [hc] at this
  have h3 : WeylBranchPieces.IsSubquotient S (T.castRank e0 Z).representation :=
    h2.of_equiv_right (T.castRankEquiv e0 Z)
  have : (T.castRank e0 Z).representation.IsIrreducible := T.isIrreducible_castRank e0 Z hZ
  exact SmoothRep.isSubquotient_iff_representation.mpr
    (FiniteTensor.isSubquotient_of_tprod_trivial (Representation.trivial ℂ _ Y₁) (fun _ => rfl)
      Y₂.representation h3)

/-- For `m₂ = 0`, an irreducible subquotient of `Y₁ × Y₂` is, after the rank transport
`m₁ + m₂ = m₁`, a subquotient of `Y₁`. -/
theorem isSubquotient_of_isSubquotient_binaryProduct_zero_right {m₁ m₂ : ℕ} (hb : m₂ = 0)
    (Y₁ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m₁ F.Carrier))
    (Y₂ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m₂ F.Carrier))
    (Z : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (m₁ + m₂) F.Carrier))
    (hZ : letI := T.topology; Z.IsIrreducible)
    (hZP : letI := T.topology;
      SmoothRep.IsSubquotient Z ((T.binaryNormalizedProductFunctor m₁ m₂).obj (Y₁, Y₂))) :
    letI := T.topology
    SmoothRep.IsSubquotient (T.castRank (by omega : m₁ + m₂ = m₁) Z) Y₁ := by
  let := T.topology
  have e0 : m₁ + m₂ = m₁ := by omega
  let r := GeneralLinear.reindex (R := F.Carrier) (finCongr e0)
  let S := BinaryTensor.firstFactor Y₁.representation Y₂
  have h1 : WeylBranchPieces.IsSubquotient (S.comp r.toMonoidHom) Z.representation :=
    WeylBranchPieces.IsSubquotient.of_equiv_left (T.binaryRightZeroTensorEquiv hb (Y₁, Y₂)).symm
      (SmoothRep.isSubquotient_iff_representation.mp hZP)
  have hc : (S.comp r.toMonoidHom).comp r.symm.toMonoidHom = S := by
    ext g v
    simp
  have h2 : WeylBranchPieces.IsSubquotient S (Z.representation.comp r.symm.toMonoidHom) := by
    have := h1.comp r.symm.toMonoidHom
    rwa [hc] at this
  have h3 : WeylBranchPieces.IsSubquotient S (T.castRank e0 Z).representation :=
    h2.of_equiv_right (T.castRankEquiv e0 Z)
  let Cm : S.Equiv (BinaryTensor.secondFactor Y₂ Y₁.representation) :=
    Representation.Equiv.mk (TensorProduct.comm ℂ Y₁ Y₂) fun g =>
      TensorProduct.ext' fun v w => by simp [S]
  have h4 : WeylBranchPieces.IsSubquotient (BinaryTensor.secondFactor Y₂ Y₁.representation)
      (T.castRank e0 Z).representation :=
    WeylBranchPieces.IsSubquotient.of_equiv_left Cm.symm h3
  have : (T.castRank e0 Z).representation.IsIrreducible := T.isIrreducible_castRank e0 Z hZ
  exact SmoothRep.isSubquotient_iff_representation.mpr
    (FiniteTensor.isSubquotient_of_tprod_trivial (Representation.trivial ℂ _ Y₂) (fun _ => rfl)
      Y₁.representation h4)

/-- A binary product of positive ranks with a zero first factor is zero. -/
theorem subsingleton_binaryProduct_of_left {m₁ m₂ : ℕ} (h₁ : 0 < m₁) (h₂ : 0 < m₂)
    (Y₁ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m₁ F.Carrier))
    (Y₂ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m₂ F.Carrier))
    [hY : Subsingleton Y₁] :
    Subsingleton ((T.binaryNormalizedProductFunctor m₁ m₂).obj (Y₁, Y₂)) := by
  let := T.topology
  obtain ⟨e⟩ := SegmentSocleDerivativesProof.nonempty_ofPairProductIso T h₁ h₂ Y₁ Y₂
  have h0 : Subsingleton (twoBlockFactors h₁ h₂ Y₁ Y₂ 0) := hY
  have hV : Subsingleton (PiTensorProduct ℂ fun i => twoBlockFactors h₁ h₂ Y₁ Y₂ i) :=
    subsingleton_piTensorProduct (V := fun i => twoBlockFactors h₁ h₂ Y₁ Y₂ i) 0
  have hQ : Subsingleton
      ((T.normalizedProductInductionFunctor (BlockShape.ofPair m₁ m₂ h₁ h₂ rfl)).obj
      (twoBlockFactors h₁ h₂ Y₁ Y₂)) := by
    refine ⟨fun a b => ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    funext x
    exact @Subsingleton.elim _ hV _ _
  exact (SmoothRep.equivOfIso e).injective.subsingleton

/-- **Clause 2** (product), assuming the per-piece statement `BinaryGeometricPieceConstituents`:
normalized products of finite-length left `A`-reduced representations are left `A`-reduced. -/
theorem leftReduced_binaryProduct
    (hPP : BinaryGeometricPieces.BinaryGeometricPieceConstituents.{uF, uV})
    {d : ℕ} (A : letI := T.topology; SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := d))
    {m₁ m₂ : ℕ}
    (Y₁ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m₁ F.Carrier))
    (Y₂ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m₂ F.Carrier))
    (hY₁ : letI := T.topology; Y₁.HasFiniteLength) (hY₂ : letI := T.topology; Y₂.HasFiniteLength)
    (hr₁ : LeftReduced F T A Y₁) (hr₂ : LeftReduced F T A Y₂) :
    LeftReduced F T A ((T.binaryNormalizedProductFunctor m₁ m₂).obj (Y₁, Y₂)) := by
  let := T.topology
  rcases Nat.eq_zero_or_pos m₁ with ha | h₁
  · exact leftReduced_of_castRank_isSubquotient F T A (by omega : m₁ + m₂ = m₂) _ Y₂
      (fun Z hZ hZP => isSubquotient_of_isSubquotient_binaryProduct_zero_left F T ha Y₁ Y₂ Z hZ hZP)
      hr₂
  rcases Nat.eq_zero_or_pos m₂ with hb | h₂
  · exact leftReduced_of_castRank_isSubquotient F T A (by omega : m₁ + m₂ = m₁) _ Y₁
      (fun Z hZ hZP => isSubquotient_of_isSubquotient_binaryProduct_zero_right F T hb Y₁ Y₂ Z hZ
        hZP)
      hr₁
  intro Z hZ hZP k h σ hsub
  have hZnt : Nontrivial Z := nontrivial_of_isIrreducible hZ
  rcases Nat.eq_zero_or_pos d with hd0 | hd
  · subst hd0
    have := subsingleton_of_leftReduced_rankZero F T A Y₁ hY₁ hr₁
    have := subsingleton_binaryProduct_of_left F T h₁ h₂ Y₁ Y₂
    exact not_isSubquotient_of_subsingleton hZP
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · subst hk0
    obtain ⟨g, hg⟩ := exists_ne_zero_of_isSubrepresentation_rankZero F T h Z A.obj σ hZnt hsub
    have hAi : (T.castRank h A.obj).representation.IsIrreducible :=
      T.isIrreducible_castRank h A.obj A.property.1
    have hgs := (Representation.IsIrreducible.surjective_or_eq_zero g).resolve_right hg
    have hAZ : SmoothRep.IsSubquotient (T.castRank h A.obj) Z :=
      SmoothRep.isSubquotient_iff_representation.mpr
        (WeylBranchPieces.IsSubquotient.of_surjective g hgs)
    obtain ⟨A', hA'⟩ := exists_supercuspidal_castRank F T h A
    apply not_isSubquotient_castRank_binaryProduct_of_supercuspidal F T h₁ h₂ rfl A' Y₁ Y₂ hY₁ hY₂
    rw [hA']
    exact SegmentHeadSupport.isSubquotient_trans hAZ hZP
  exact false_of_isSubquotient_binaryProduct_of_pos F T hPP hd hk h₁ h₂ h A Y₁ Y₂ hY₁ hY₂ hr₁ hr₂
    Z hZ hZP σ hsub

end Wrapper

end Langlands.Classification.LeftCuspidalDerivative
