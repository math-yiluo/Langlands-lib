import Langlands.Representation.Exponents.WeylBranchPiecesStatement
import Langlands.Representation.Geometric.InducedOppositeCuspidalPieceStatement
import Langlands.Representation.Classification.ProductLeviCuspidalJacquetAssembly
import Langlands.Representation.Parabolic.RefinedInductionTensorProof
import Langlands.Representation.CuspidalSupport.AssociatedGeometricPiecesEquivalenceProof
import Langlands.Representation.Tensor.ExternalSubquotient

/-!
# The cuspidal-induction Jacquet constituent from cuspidal geometric pieces

An irreducible cuspidal actual subquotient of the inner opposite Jacquet module
of the inner normalized induction of an irreducible cuspidal representation is a
block-diagonal Weyl transport of the inducing representation, assuming the
general-linear cuspidal-piece statement
`GLInducedOppositeJacquetCuspidalPieceStatement`.
-/

noncomputable section

namespace Langlands.CuspidalInductionJacquetConstituent

open GeneralLinear Geometric CuspidalSupport WeylBranchPieces
open RelativeJacquetMultiplicity

universe uF uV uW

section Subquotient

variable {G : Type*} [Group G] {H : Type*} [Group H] {V W : Type*}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- An irreducible actual subquotient of an irreducible representation is
equivalent to it. -/
theorem nonempty_equiv_of_isSubquotient {A : Representation ℂ G V}
    {Y : Representation ℂ G W} (hA : A.IsIrreducible) (hY : Y.IsIrreducible)
    (h : IsSubquotient A Y) : Nonempty (A.Equiv Y) := by
  obtain ⟨U, q, hq⟩ := h
  have : Nontrivial W := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) Y.asModule
  obtain ⟨y, hy⟩ := exists_ne (0 : W)
  rcases eq_bot_or_eq_top U with rfl | rfl
  · exfalso
    obtain ⟨u, rfl⟩ := hq y
    apply hy
    have hu : u = 0 := Subtype.ext ((Submodule.mem_bot ℂ).1 u.property)
    rw [hu, map_zero]
  · let ι : A.IntertwiningMap (⊤ : Subrepresentation A).toRepresentation :=
      { toLinearMap :=
          { toFun := fun v => ⟨v, Submodule.mem_top⟩
            map_add' := fun _ _ => rfl
            map_smul' := fun _ _ => rfl }
        isIntertwining' := fun _ => rfl }
    let f := q.comp ι
    have hf : Function.Surjective f := fun z => by
      obtain ⟨u, hu⟩ := hq z
      exact ⟨u.val, hu⟩
    have hb : Function.Bijective f := by
      refine (Representation.IsIrreducible.bijective_or_eq_zero f).resolve_right fun h0 => hy ?_
      obtain ⟨v, hv⟩ := hf y
      rw [← hv, h0]
      rfl
    exact ⟨f.ofBijective hb⟩

/-- Subquotients may be tested after restriction along a group isomorphism. -/
theorem isSubquotient_of_comp_equiv {A : Representation ℂ G V}
    {Y : Representation ℂ G W} (e : H ≃* G)
    (h : IsSubquotient (A.comp e.toMonoidHom) (Y.comp e.toMonoidHom)) :
    IsSubquotient A Y := by
  have h' := h.comp e.symm.toMonoidHom
  have hA : (A.comp e.toMonoidHom).comp e.symm.toMonoidHom = A := by
    ext g v
    simp
  have hY : (Y.comp e.toMonoidHom).comp e.symm.toMonoidHom = Y := by
    ext g v
    simp
  rwa [hA, hY] at h'

end Subquotient

section FullRefinement

variable {K : Type*} [Field K] {m : ℕ} (B C : BlockShape m) (S : BlockRefinement B)

/-- A refinement with full refined Levi has the same embedded Levi as the coarse
shape. -/
theorem leviSubgroup_flatten_of_full (h : refinedLevi K B S = ⊤) :
    (B.flatten S).leviSubgroup K = B.leviSubgroup K := by
  ext g
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(flattenedLeviEquiv K B S x).val, flattenedLeviEquiv_embedding K B S x⟩
  · rintro ⟨x, rfl⟩
    exact ⟨(flattenedLeviEquiv K B S).symm ⟨x, h ▸ Subgroup.mem_top x⟩,
      flattenedLeviEquiv_symm_embedding K B S _⟩

theorem conjugatesLevi_of_full (h : refinedLevi K B S = ⊤) (w : Equiv.Perm (Fin m))
    (hw : ConjugatesLevi (F := K) (B.flatten S) C w) : ConjugatesLevi (F := K) B C w := by
  unfold ConjugatesLevi at hw ⊢
  rwa [leviSubgroup_flatten_of_full B S h] at hw

/-- With a full refined Levi, inverse conjugation from the flattened shape is
inverse conjugation from the coarse shape. -/
theorem flattenedLeviEquiv_leviConjugation_symm_of_full (h : refinedLevi K B S = ⊤)
    (w : Equiv.Perm (Fin m)) (hw : ConjugatesLevi (F := K) (B.flatten S) C w)
    (x : C.Levi K) :
    (flattenedLeviEquiv K B S ((leviConjugation (B.flatten S) C w hw).symm x)).val =
      (leviConjugation B C w (conjugatesLevi_of_full B C S h w hw)).symm x := by
  apply B.leviEmbedding_injective K
  rw [flattenedLeviEquiv_embedding, leviConjugation_symm_embedding,
    leviConjugation_symm_embedding]

theorem transport_comp_flattenedLeviEquiv_of_full {V : Type*} [AddCommGroup V] [Module ℂ V]
    (h : refinedLevi K B S = ⊤) (w : Equiv.Perm (Fin m))
    (hw : ConjugatesLevi (F := K) (B.flatten S) C w) (π : Representation ℂ (B.Levi K) V) :
    transport (B.flatten S) C w hw
        (π.comp ((refinedLevi K B S).subtype.comp (flattenedLeviEquiv K B S).toMonoidHom)) =
      transport B C w (conjugatesLevi_of_full B C S h w hw) π := by
  refine MonoidHom.ext fun x => ?_
  change π (flattenedLeviEquiv K B S ((leviConjugation (B.flatten S) C w hw).symm x)).val =
    π ((leviConjugation B C w (conjugatesLevi_of_full B C S h w hw)).symm x)
  rw [flattenedLeviEquiv_leviConjugation_symm_of_full B C S h w hw]

theorem surjective_subtype_comp_flattenedLeviEquiv_of_full (h : refinedLevi K B S = ⊤) :
    Function.Surjective
      ((refinedLevi K B S).subtype.comp (flattenedLeviEquiv K B S).toMonoidHom) := by
  intro x
  refine ⟨(flattenedLeviEquiv K B S).symm ⟨x, h ▸ Subgroup.mem_top x⟩, ?_⟩
  change ((flattenedLeviEquiv K B S) ((flattenedLeviEquiv K B S).symm _)).val = x
  rw [MulEquiv.apply_symm_apply]

end FullRefinement

section GeneralLinearStep

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- General-linear constituent step: an irreducible cuspidal actual subquotient of
the opposite Jacquet module of the normalized induction of an irreducible cuspidal
representation is equivalent to a Weyl transport of it. -/
theorem exists_equiv_transport_of_cuspidalPiece
    (hP : GLInducedOppositeJacquetCuspidalPieceStatement.{uF, uW, uV})
    {m : ℕ} (hm : 0 < m) (B C : BlockShape m)
    {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (B.Levi F.Carrier) V) (ρ : Representation ℂ (C.Levi F.Carrier) W) :
    letI := T.topology
    IsSmooth π → π.IsIrreducible → IsLeviCuspidal B π →
      ρ.IsIrreducible → IsLeviCuspidal C ρ →
      IsSubquotient (CuspidalJacquetMultiplicity.oppositeJacquet T C
        (CuspidalJacquetMultiplicity.induced T B (Rep.of π))).ρ ρ →
      ∃ (w : Equiv.Perm (Fin m)) (hw : ConjugatesLevi (F := F.Carrier) B C w),
        Nonempty (ρ.Equiv (transport B C w hw π)) := by
  let := T.topology
  intro hπs hπ hπc hρ hρc h
  obtain ⟨S, w, hw, U, q, hq⟩ := hP p F T m hm B C (Rep.of π) hπs (Rep.of ρ) hρ hρc h
  have : Nontrivial W := by
    have := hρ
    exact IsSimpleModule.nontrivial (MonoidAlgebra ℂ (C.Levi F.Carrier)) ρ.asModule
  have hfull : refinedParabolic F.Carrier B S = ⊤ := by
    by_contra hne
    have hsub : Subsingleton (RefinedJacquetModule B S π) := hπc.2 S hne
    obtain ⟨y, hy⟩ := exists_ne (0 : W)
    obtain ⟨u, rfl⟩ := hq y
    apply hy
    have hu : u = 0 := Subtype.ext (Subsingleton.elim _ _)
    rw [hu, map_zero]
  have hL : refinedLevi F.Carrier B S = ⊤ :=
    refinedLevi_eq_top_of_refinedParabolic_eq_top B S hfull
  let ψ := (refinedLevi F.Carrier B S).subtype.comp
    (flattenedLeviEquiv F.Carrier B S).toMonoidHom
  let Jf := (T.normalizedRefinedJacquet B S π).comp
    (flattenedLeviEquiv F.Carrier B S).toMonoidHom
  let eJ : Representation.Equiv Jf (π.comp ψ) :=
    FiniteTensorFiltration.compCongr (fullRefinedJacquetEquiv T B S hL π) _
  have hsq : IsSubquotient (transport (B.flatten S) C w hw Jf) ρ :=
    ⟨{ toSubmodule := U.toSubmodule
       apply_mem_toSubmodule := fun g _ hv => U.apply_mem_toSubmodule _ hv },
      { toLinearMap := q.toLinearMap
        isIntertwining' := q.isIntertwining' }, hq⟩
  have hJ : (transport (B.flatten S) C w hw Jf).IsIrreducible :=
    JacquetLength.isIrreducible_transport w hw
      (JacquetLength.isIrreducible_of_equiv eJ.symm
        (JacquetLength.isIrreducible_comp ψ
          (surjective_subtype_comp_flattenedLeviEquiv_of_full B S hL) hπ))
  obtain ⟨E⟩ := nonempty_equiv_of_isSubquotient hJ hρ hsq
  refine ⟨w, conjugatesLevi_of_full B C S hL w hw, ?_⟩
  rw [← transport_comp_flattenedLeviEquiv_of_full B C S hL w hw π]
  exact ⟨E.symm.trans (FiniteTensorFiltration.compCongr eJ _)⟩

end GeneralLinearStep

section Blocks

variable {K : Type*} [Field K] {n : ℕ} (D : BlockShape n) (R R' : BlockRefinement D)

/-- Blockwise conjugating permutations assemble to a block-diagonal permutation
conjugating the flattened Levis. -/
theorem conjugatesLevi_flatten_blockPermOf (σ : ∀ i, Equiv.Perm (Fin (D.size i)))
    (hσ : ∀ i, ConjugatesLevi (F := K) (R i) (R' i) (σ i)) :
    ConjugatesLevi (F := K) (D.flatten R) (D.flatten R') (blockPermOf D σ) := by
  rw [TotalConjugatingCount.conjugatesLevi_iff]
  intro a b
  obtain ⟨i, x, rfl⟩ := TotalConjugatingCount.index_surjective D a
  obtain ⟨i', y, rfl⟩ := TotalConjugatingCount.index_surjective D b
  rw [blockPermOf_index, blockPermOf_index]
  by_cases hi : i = i'
  · subst i'
    rw [ProductLeviMinimalIndex.blockIndex_flatten_index_eq_iff,
      ProductLeviMinimalIndex.blockIndex_flatten_index_eq_iff]
    exact (TotalConjugatingCount.conjugatesLevi_iff (F := K) _ _ _).mp (hσ i) x y
  · exact iff_of_false (ProductLeviMinimalIndex.blockIndex_flatten_index_ne D R hi x y)
      (ProductLeviMinimalIndex.blockIndex_flatten_index_ne D R' hi _ _)

theorem nestedEmbedding_injective (S : BlockRefinement D) :
    Function.Injective (fun X : ∀ i, (S i).Levi K =>
      D.leviEmbedding K (refinedLeviEquiv K D S X).val) :=
  fun _ _ h => (refinedLeviEquiv K D S).injective
    (Subtype.ext (D.leviEmbedding_injective K h))

/-- In flattened product coordinates, conjugation by an assembled block-diagonal
permutation is blockwise conjugation. -/
theorem flattenedLeviProductEquiv_leviConjugation (σ : ∀ i, Equiv.Perm (Fin (D.size i)))
    (hσ : ∀ i, ConjugatesLevi (F := K) (R i) (R' i) (σ i))
    (hw : ConjugatesLevi (F := K) (D.flatten R) (D.flatten R') (blockPermOf D σ))
    (x : (D.flatten R).Levi K) :
    flattenedLeviProductEquiv K D R'
        (leviConjugation (D.flatten R) (D.flatten R') (blockPermOf D σ) hw x) =
      fun i => leviConjugation (R i) (R' i) (σ i) (hσ i)
        (flattenedLeviProductEquiv K D R x i) := by
  apply nestedEmbedding_injective D R'
  have hflat : ∀ (S : BlockRefinement D) (y : (D.flatten S).Levi K),
      D.leviEmbedding K (refinedLeviEquiv K D S (flattenedLeviProductEquiv K D S y)).val =
        (D.flatten S).leviEmbedding K y := fun S => flattenedLeviEquiv_embedding K D S
  simp only
  rw [hflat R', leviConjugation_embedding, ← hflat R]
  change _ = D.leviEmbedding K (fun i => (R' i).leviEmbedding K
    (leviConjugation (R i) (R' i) (σ i) (hσ i) (flattenedLeviProductEquiv K D R x i)))
  simp only [leviConjugation_embedding]
  rw [ProductLeviMinimalIndex.leviEmbedding_conj_blockPermOf]
  rfl

/-- The inverse conjugations used by transport are also blockwise. -/
theorem flattenedLeviProductEquiv_leviConjugation_symm
    (σ : ∀ i, Equiv.Perm (Fin (D.size i)))
    (hσ : ∀ i, ConjugatesLevi (F := K) (R i) (R' i) (σ i))
    (hw : ConjugatesLevi (F := K) (D.flatten R) (D.flatten R') (blockPermOf D σ))
    (x : (D.flatten R').Levi K) :
    flattenedLeviProductEquiv K D R
        ((leviConjugation (D.flatten R) (D.flatten R') (blockPermOf D σ) hw).symm x) =
      fun i => (leviConjugation (R i) (R' i) (σ i) (hσ i)).symm
        (flattenedLeviProductEquiv K D R' x i) := by
  set x' := (leviConjugation (D.flatten R) (D.flatten R') (blockPermOf D σ) hw).symm x
  have hx : x = leviConjugation (D.flatten R) (D.flatten R') (blockPermOf D σ) hw x' := by
    rw [MulEquiv.apply_symm_apply]
  rw [hx, flattenedLeviProductEquiv_leviConjugation D R R' σ hσ hw]
  funext i
  rw [MulEquiv.symm_apply_apply]

/-- The external tensor product of blockwise transports is the external tensor
product pulled back along the blockwise inverse conjugations. -/
theorem external_transport {X : Fin D.length → Type*} [∀ i, AddCommGroup (X i)]
    [∀ i, Module ℂ (X i)] (A : ∀ i, Representation ℂ ((R i).Levi K) (X i))
    (σ : ∀ i, Equiv.Perm (Fin (D.size i)))
    (hσ : ∀ i, ConjugatesLevi (F := K) (R i) (R' i) (σ i)) (y : ∀ i, (R' i).Levi K) :
    FiniteTensor.external (fun i => transport (R i) (R' i) (σ i) (hσ i) (A i)) y =
      FiniteTensor.external A
        (fun i => (leviConjugation (R i) (R' i) (σ i) (hσ i)).symm (y i)) := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  simp only [LinearMap.compMultilinearMap_apply, FiniteTensor.external_tprod, transport,
    MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]

/-- Blockwise transports of the factors of `ω`, in flattened product coordinates,
are the transport of `ω` by the assembled block-diagonal permutation. -/
def blockTransportEquiv {V : Type*} [AddCommGroup V] [Module ℂ V]
    {X : Fin D.length → Type*} [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]
    (ω : Representation ℂ ((D.flatten R).Levi K) V)
    (A : ∀ i, Representation ℂ ((R i).Levi K) (X i))
    (E : ω.Equiv ((FiniteTensor.external A).comp (flattenedLeviProductEquiv K D R).toMonoidHom))
    (σ : ∀ i, Equiv.Perm (Fin (D.size i)))
    (hσ : ∀ i, ConjugatesLevi (F := K) (R i) (R' i) (σ i))
    (hw : ConjugatesLevi (F := K) (D.flatten R) (D.flatten R') (blockPermOf D σ)) :
    Representation.Equiv
      ((FiniteTensor.external fun i => transport (R i) (R' i) (σ i) (hσ i) (A i)).comp
        (flattenedLeviProductEquiv K D R').toMonoidHom)
      (transport (D.flatten R) (D.flatten R') (blockPermOf D σ) hw ω) :=
  Representation.Equiv.mk E.symm.toLinearEquiv fun x => by
    have h := E.symm.isIntertwining'
      ((leviConjugation (D.flatten R) (D.flatten R') (blockPermOf D σ) hw).symm x)
    have hc := flattenedLeviProductEquiv_leviConjugation_symm D R R' σ hσ hw x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at h ⊢
    rw [external_transport, transport, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← hc]
    exact h

theorem refinedLeviEquiv_symm_comp_flattenedLeviEquiv (S : BlockRefinement D) :
    (refinedLeviEquiv K D S).symm.toMonoidHom.comp (flattenedLeviEquiv K D S).toMonoidHom =
      (flattenedLeviProductEquiv K D S).toMonoidHom := by
  refine MonoidHom.ext fun x => ?_
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, flattenedLeviEquiv,
    MulEquiv.trans_apply, MulEquiv.symm_apply_apply]

end Blocks

end Langlands.CuspidalInductionJacquetConstituent

namespace Langlands

open GeneralLinear Geometric CuspidalSupport WeylBranchPieces
open RelativeJacquetMultiplicity CuspidalInductionJacquetConstituent

universe uF uV uW

/-- The cuspidal-induction Jacquet constituent statement follows from the
general-linear cuspidal-piece statement. -/
theorem glCuspidalInductionJacquetConstituent_of_cuspidalPiece
    (hP : GLInducedOppositeJacquetCuspidalPieceStatement.{uF, uW, uV}) :
    GLCuspidalInductionJacquetConstituentStatement.{uF, uV, uW} := by
  intro p _ F T n hn D R R' ω hω hωc ρ hρ hρc h
  let := T.topology
  let := T.leviTopologicalGroup D
  obtain ⟨A, hA, ⟨E⟩⟩ := ProductLeviCuspidalJacquetAssembly.exists_factors T D R hn ω.ρ hω hωc
  obtain ⟨A', hA', ⟨E'⟩⟩ :=
    ProductLeviCuspidalJacquetAssembly.exists_factors T D R' hn ρ.ρ hρ hρc
  obtain ⟨⟨E3, -⟩⟩ := Parabolic.refinedInductionTensor p F T n D R A
  let I := innerInduced T D R
    (Rep.of (ω.ρ.comp (flattenedLeviEquiv F.Carrier D R).symm.toMonoidHom))
  let X : I.ρ.Equiv (Parabolic.RefinedInductionTensor.externalRepresentation F T D R A) :=
    (ProductLeviCuspidalJacquetAssembly.normalizedRefinedInducedCongr T D R
      (ProductLeviCuspidalJacquetAssembly.inducingEquiv T D R E)).trans E3
  let Ai : ∀ i, Rep.{max uF uV} ℂ (GeneralLinear (D.size i) F.Carrier) := fun i =>
    CuspidalJacquetMultiplicity.induced T (R i) (Rep.of (A i).representation)
  let Jo : ∀ i, Rep.{max uF uV} ℂ ((R' i).Levi F.Carrier) := fun i =>
    CuspidalJacquetMultiplicity.oppositeJacquet T (R' i) (Ai i)
  let φ := (refinedLeviEquiv F.Carrier D R').symm.toMonoidHom
  let Kq : (innerJacquet T D R' I).ρ.Equiv ((FiniteTensor.external fun i => (Jo i).ρ).comp φ) :=
    (RefinedOppositeJacquetTensor.normalizedRefinedOppositeJacquetCongr T D R' X).trans
      (RefinedOppositeJacquetTensor.oppositeJacquetEquiv T D R' Ai)
  have K' := FiniteTensorFiltration.compCongr Kq (flattenedLeviEquiv F.Carrier D R').toMonoidHom
  have hK : ((FiniteTensor.external fun i => (Jo i).ρ).comp φ).comp
        (flattenedLeviEquiv F.Carrier D R').toMonoidHom =
      (FiniteTensor.external fun i => (Jo i).ρ).comp
        (flattenedLeviProductEquiv F.Carrier D R').toMonoidHom := by
    rw [← refinedLeviEquiv_symm_comp_flattenedLeviEquiv]
    rfl
  rw [hK] at K'
  have h1 : IsSubquotient
      ((FiniteTensor.external fun i => (Jo i).ρ).comp
        (flattenedLeviProductEquiv F.Carrier D R').toMonoidHom)
      ((FiniteTensor.external fun i => (A' i).representation).comp
        (flattenedLeviProductEquiv F.Carrier D R').toMonoidHom) :=
    IsSubquotient.of_equiv_left K'.symm (h.of_equiv_right E')
  have h2 := isSubquotient_of_comp_equiv (flattenedLeviProductEquiv F.Carrier D R') h1
  have h3 : ∀ i, IsSubquotient (Jo i).ρ (A' i).representation :=
    FiniteTensor.isSubquotient_factor_of_external _ _ (fun i => (hA' i).1) h2
  have h4 : ∀ i, ∃ (w : Equiv.Perm (Fin (D.size i)))
      (hw : ConjugatesLevi (F := F.Carrier) (R i) (R' i) w),
      Nonempty ((A' i).representation.Equiv
        (transport (R i) (R' i) w hw (A i).representation)) := fun i =>
    exists_equiv_transport_of_cuspidalPiece T hP (D.positive i) (R i) (R' i)
      (A i).representation (A' i).representation (A i).isSmooth (hA i).1 (hA i).2
      (hA' i).1 (hA' i).2 (h3 i)
  choose σ hσ e using h4
  have hw := conjugatesLevi_flatten_blockPermOf D R R' σ hσ
  refine ⟨blockPermOf D σ, blockPermOf_mem_blockWeyl D σ, hw, ⟨?_⟩⟩
  exact E'.trans ((FiniteTensorFiltration.compCongr
    (FiniteTensorFiltration.externalCongr fun i => (e i).some) _).trans
      (blockTransportEquiv D R R' ω.ρ _ E σ hσ hw))

end Langlands
