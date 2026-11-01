import Langlands.Representation.CuspidalSupport.WholeLeviTransport
import Langlands.Representation.Geometric.GeometricLemmaProof
import Langlands.Representation.Geometric.FlattenedLevi
import Langlands.Representation.CuspidalSupport.JacquetVanishingHelpers
import Langlands.Representation.CuspidalSupport.AssociatedGeometricPiecesEquivalenceProof
import Langlands.Representation.CuspidalSupport.MinimalConjugatingCosetsProof
import Langlands.Representation.CuspidalSupport.AssociationReduction
import Langlands.Representation.CuspidalSupport.MinimalWeylTransportProof
import Langlands.Representation.CuspidalSupport.LeviTensorFactorizationProof
import Langlands.Representation.CuspidalSupport.CuspidalTensorProof
import Langlands.Representation.CuspidalSupport.CuspidalTensorAssociationProof
import Langlands.Representation.Parabolic.RefinedInductionTensorProof
import Langlands.Representation.Tensor.FlattenedGLRefinement
import Langlands.Representation.Shahidi.TwoBlocks
import Langlands.Representation.Derivative.PartialDerivativeJacquetComparisonProof

/-! Irreducible quotients of derivatives of cuspidal products: unshifted support. -/

noncomputable section

namespace Langlands.Classification.CuspidalProductDerivativeQuotientSupport

open CategoryTheory GeneralLinear Geometric CuspidalSupport

universe uF uV uW uR uG uC vC

section Filtration

variable {R : Type uR} {G : Type uG} [CommRing R] [Monoid G]
  {C : Type uC} [Category.{vC} C]

/-- A nonzero linear map out of the top of a finite natural filtration, equivariant
along a monoid homomorphism into the acting monoid, gives such a nonzero map out of
some successive quotient. -/
theorem exists_graded_map {F : C ⥤ Rep.{uV} R G} {n : ℕ}
    (s : RepFunctorFiltration F n) (X : C)
    {H : Type*} [Monoid H] (ι : H → G) {W : Type uW} [AddCommGroup W] [Module R W]
    (π : Representation R H W) (φ : (F.obj X) →ₗ[R] W) (hφ : φ ≠ 0)
    (heq : ∀ h v, φ ((F.obj X).ρ (ι h) v) = π h (φ v)) :
    ∃ i : Fin n, ∃ ψ : ((s.graded i).obj X) →ₗ[R] W, ψ ≠ 0 ∧
      ∀ h v, ψ (((s.graded i).obj X).ρ (ι h) v) = π h (ψ v) := by
  classical
  let res : Fin (n + 1) → Prop := fun j => ∀ v ∈ ((s.step j).obj X).toSubmodule, φ v = 0
  have h0 : res 0 := by
    intro v hv
    have hv' : v ∈ ((⊥ : Subrepresentation (F.obj X).ρ)).toSubmodule := by
      rw [← s.zero X]; exact hv
    have : v = 0 := hv'
    rw [this, map_zero]
  have hlast : ¬ res (Fin.last n) := by
    intro h
    apply hφ
    ext v
    apply h v
    rw [s.top X]
    trivial
  have key : ∃ i : Fin n, res i.castSucc ∧ ¬ res i.succ := by
    by_contra hk
    push Not at hk
    have hall : ∀ j : ℕ, (hj : j ≤ n) → res ⟨j, Nat.lt_succ_of_le hj⟩ := by
      intro j
      induction j with
      | zero => intro _; exact h0
      | succ j ih => intro hj; exact hk ⟨j, by omega⟩ (ih (by omega))
    exact hlast (hall n le_rfl)
  obtain ⟨i, hlow, hhigh⟩ := key
  let U := (s.step i.succ).obj X
  let L := (s.step i.castSucc).lowerInUpper (s.step i.succ) X
  let φU : U.toSubmodule →ₗ[R] W := φ.comp U.toSubmodule.subtype
  have hker : L.toSubmodule ≤ LinearMap.ker φU := by
    intro v hv
    exact hlow v.val hv
  refine ⟨i, L.toSubmodule.liftQ φU hker, ?_, ?_⟩
  · intro hz
    apply hhigh
    intro v hv
    have := LinearMap.congr_fun hz (L.toSubmodule.mkQ ⟨v, hv⟩)
    change (L.toSubmodule.liftQ φU hker) (L.toSubmodule.mkQ ⟨v, hv⟩) = (0 : W) at this
    simp only [Submodule.mkQ_apply, Submodule.liftQ_apply] at this
    exact this
  · intro h v
    obtain ⟨v, rfl⟩ := L.toSubmodule.mkQ_surjective v
    change φ ((F.obj X).ρ (ι h) v.val) = π h (φ v.val)
    exact heq h v.val

/-- Transfer of an equivariant nonzero linear map along an isomorphism of
representations. -/
theorem exists_map_of_iso {A B : Rep.{uV} R G} (e : A ≅ B)
    {H : Type*} [Monoid H] (ι : H → G) {W : Type uW} [AddCommGroup W] [Module R W]
    (π : Representation R H W) (ψ : A →ₗ[R] W) (hψ : ψ ≠ 0)
    (heq : ∀ h v, ψ (A.ρ (ι h) v) = π h (ψ v)) :
    ∃ χ : B →ₗ[R] W, χ ≠ 0 ∧ ∀ h v, χ (B.ρ (ι h) v) = π h (χ v) := by
  refine ⟨ψ.comp e.inv.hom.toLinearMap, ?_, ?_⟩
  · intro hz
    apply hψ
    ext v
    have := LinearMap.congr_fun hz (e.hom.hom v)
    simpa using this
  · intro h v
    change ψ (e.inv.hom (B.ρ (ι h) v)) = π h (ψ (e.inv.hom v))
    rw [Rep.hom_comm_apply e.inv (ι h) v]
    exact heq h _

end Filtration

section Geometry

variable {F : Type uF} [Field F] {n : ℕ} (B C : BlockShape n)

/-- Ambient membership in the flattened Levi is exactly refined membership. -/
theorem leviEmbedding_mem_flattenedLevi_iff (S : BlockRefinement B) (m : B.Levi F) :
    B.leviEmbedding F m ∈ (B.flatten S).leviSubgroup F ↔ m ∈ refinedLevi F B S := by
  constructor
  · rintro ⟨d, hd⟩
    have hm : (flattenedLeviEquiv F B S d).val = m :=
      B.leviEmbedding_injective F ((flattenedLeviEquiv_embedding F B S d).trans hd)
    exact hm ▸ (flattenedLeviEquiv F B S d).property
  · intro hm
    exact ⟨(flattenedLeviEquiv F B S).symm ⟨m, hm⟩,
      flattenedLeviEquiv_symm_embedding F B S ⟨m, hm⟩⟩

/-- The fine block diagonal subgroup lies in the coarse block diagonal subgroup. -/
theorem flattenedLeviSubgroup_le (S : BlockRefinement B) :
    (B.flatten S).leviSubgroup F ≤ B.leviSubgroup F := by
  rintro g ⟨d, rfl⟩
  exact ⟨(flattenedLeviEquiv F B S d).val, flattenedLeviEquiv_embedding F B S d⟩

/-- If the source intersection is a refined Levi and the target intersection is
the whole target Levi, the flattened source refinement is conjugated onto the
target Levi. -/
theorem conjugatesLevi_flatten_of_target_top (S : BlockRefinement B)
    (w : Equiv.Perm (Fin n))
    (hS : sourceLevi F B C w = refinedLevi F B S)
    (hR : sourceLevi F C B w⁻¹ = ⊤) :
    ConjugatesLevi (F := F) (B.flatten S) C w := by
  apply Subgroup.ext
  intro g
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨m, rfl⟩ := flattenedLeviSubgroup_le B S hx
    have hm : m ∈ sourceLevi F B C w :=
      hS ▸ (leviEmbedding_mem_flattenedLevi_iff B S m).mp hx
    exact hm
  · rintro ⟨m', rfl⟩
    have hm' : m' ∈ sourceLevi F C B w⁻¹ := hR ▸ Subgroup.mem_top m'
    obtain ⟨m, hm⟩ := hm'
    have key : (MulAut.conj (permutation n F w)).toMonoidHom (B.leviEmbedding F m) =
        C.leviEmbedding F m' := by
      change permutation n F w * B.leviEmbedding F m * (permutation n F w)⁻¹ = _
      change B.leviEmbedding F m =
        permutation n F w⁻¹ * C.leviEmbedding F m' * (permutation n F w⁻¹)⁻¹ at hm
      rw [hm, map_inv]
      group
    refine ⟨B.leviEmbedding F m, (leviEmbedding_mem_flattenedLevi_iff B S m).mpr ?_, key⟩
    rw [← hS]
    change (MulAut.conj (permutation n F w)).toMonoidHom (B.leviEmbedding F m) ∈
      C.leviSubgroup F
    rw [key]
    exact ⟨m', rfl⟩

/-- If the whole source Levi meets the target Levi after conjugation, and the
target intersection is a refined Levi of `C`, then the whole source Levi is
conjugated onto the flattened target refinement. -/
theorem conjugatesLevi_flatten_of_source_top (R : BlockRefinement C)
    (w : Equiv.Perm (Fin n))
    (hS : sourceLevi F B C w = ⊤)
    (hR : sourceLevi F C B w⁻¹ = refinedLevi F C R) :
    ConjugatesLevi (F := F) B (C.flatten R) w := by
  have h := conjugatesLevi_flatten_of_target_top C B R w⁻¹ hR (by rw [inv_inv]; exact hS)
  have h' := conjugatesLevi_inv h
  rwa [inv_inv] at h'

end Geometry

section Piece

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- Relabelling along an equality of subgroups, in the coordinates of a
homomorphism out of the target subgroup. -/
def subgroupEqualityEquivOf {G : Type uF} [Group G] [TopologicalSpace G]
    {M : Type*} [Monoid M] {V : Type*} [AddCommGroup V] [Module ℂ V]
    (H K : Subgroup G) (h : H = K) (A : SmoothRep.{0, uF, uW} ℂ H)
    (τ : Representation ℂ M V) (ψ : K →* M)
    (e : A.representation.Equiv (τ.comp (ψ.comp (MulEquiv.subgroupCongr h).toMonoidHom))) :
    ((subgroupEqualityFunctor H K h).obj A).representation.Equiv (τ.comp ψ) := by
  subst K
  exact e

/-- Intersection transport of the restriction of a source Levi representation,
when the whole source Levi is conjugated onto a third Levi `D`, read through a
homomorphism from the target intersection to `D` compatible with the ambient
embeddings. -/
def intersectionTransportEquivTo {G : Type uF} [Field G] {n : ℕ}
    (B C D : BlockShape n) (w : Equiv.Perm (Fin n))
    (hw : ConjugatesLevi (F := G) B D w) (ψ : sourceLevi G C B w⁻¹ →* D.Levi G)
    (hψ : ∀ x, D.leviEmbedding G (ψ x) = C.leviEmbedding G x.val)
    {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (sourceLevi G B C w) W) (ρ : Representation ℂ (B.Levi G) V)
    (e : σ.Equiv (ρ.comp (sourceLevi G B C w).subtype)) :
    (intersectionTransport G B C w σ).Equiv ((transport B D w hw ρ).comp ψ) := by
  have key : ∀ m : sourceLevi G C B w⁻¹,
      ((intersectionLeviConjugation G B C w).symm m).val =
        (leviConjugation B D w hw).symm (ψ m) := by
    intro m
    apply B.leviEmbedding_injective G
    rw [intersectionLeviConjugation_symm_embedding, leviConjugation_symm_embedding, hψ]
  refine Representation.Equiv.mk e.toLinearEquiv ?_
  intro m
  apply LinearMap.ext
  intro v
  have he := LinearMap.congr_fun
    (e.isIntertwining' ((intersectionLeviConjugation G B C w).symm m)) v
  change e (σ ((intersectionLeviConjugation G B C w).symm m) v) =
    ρ ((leviConjugation B D w hw).symm (ψ m)) (e v)
  change e (σ ((intersectionLeviConjugation G B C w).symm m) v) =
    ρ ((intersectionLeviConjugation G B C w).symm m).val (e v) at he
  rw [key] at he
  exact he

/-- An equivalence of representations of the refined Levi induces an equivalence of
their normalized refined inductions. -/
def normalizedRefinedInducedCongr {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)
    {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (refinedLevi F.Carrier B S) V}
    {τ : Representation ℂ (refinedLevi F.Carrier B S) W} (E : σ.Equiv τ) :
    letI := T.topology
    letI := T.leviTopologicalGroup B
    (T.normalizedRefinedInduced B S σ).Equiv (T.normalizedRefinedInduced B S τ) := by
  let := T.topology
  let := T.leviTopologicalGroup B
  exact Representation.Equiv.mk
    (LinearEquiv.ofLinearMap
      (T.normalizedRefinedInducedMap B S E.toIntertwiningMap).toLinearMap
      (T.normalizedRefinedInducedMap B S E.symm.toIntertwiningMap).toLinearMap
      (by
        apply LinearMap.ext
        intro f
        apply Subtype.ext
        apply Subtype.ext
        funext x
        exact E.apply_symm_apply _)
      (by
        apply LinearMap.ext
        intro f
        apply Subtype.ext
        apply Subtype.ext
        funext x
        exact E.symm_apply_apply _))
    (T.normalizedRefinedInducedMap B S E.toIntertwiningMap).isIntertwining'

variable {n : ℕ} (B C : BlockShape n) (w : Equiv.Perm (Fin n))
  (S : BlockRefinement B) (R : BlockRefinement C)
  (hS : sourceLevi F.Carrier B C w = refinedLevi F.Carrier B S)
  (hR : sourceLevi F.Carrier C B w⁻¹ = refinedLevi F.Carrier C R)

set_option maxHeartbeats 1200000 in
/-- When the source refinement is the whole source Levi, the geometric piece is
the normalized refined induction of the whole source representation, transported
onto the flattened target refinement. -/
def fullSourcePieceEquiv (hfull : refinedLevi F.Carrier B S = ⊤)
    (hw : ConjugatesLevi (F := F.Carrier) B (C.flatten R) w) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier),
      ((geometricPieceFunctor T B C w S R hS hR).obj A).ρ.Equiv
        (T.normalizedRefinedInduced C R
          ((transport B (C.flatten R) w hw A.representation).comp
            (flattenedLeviEquiv F.Carrier C R).symm.toMonoidHom)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro A
  let J := (T.normalizedRefinedJacquetFunctor B S).obj A
  have eJ : J.representation.Equiv
      (A.representation.comp (refinedLevi F.Carrier B S).subtype) :=
    fullRefinedJacquetEquiv T B S hfull A.representation
  let J' := (subgroupEqualityFunctor _ _ hS.symm).obj J
  have eJ' : J'.representation.Equiv
      (A.representation.comp (sourceLevi F.Carrier B C w).subtype) :=
    subgroupEqualityEquiv _ _ hS.symm J A.representation eJ
  let e := flattenedLeviEquiv F.Carrier C R
  let ψ : sourceLevi F.Carrier C B w⁻¹ →* (C.flatten R).Levi F.Carrier :=
    e.symm.toMonoidHom.comp (MulEquiv.subgroupCongr hR).toMonoidHom
  have hψ : ∀ x, (C.flatten R).leviEmbedding F.Carrier (ψ x) =
      C.leviEmbedding F.Carrier x.val := by
    intro x
    exact flattenedLeviEquiv_symm_embedding F.Carrier C R (MulEquiv.subgroupCongr hR x)
  let τ := transport B (C.flatten R) w hw A.representation
  let Q := (intersectionTransportFunctor F.Carrier B C w).obj J'
  have eQ : Q.representation.Equiv (τ.comp ψ) :=
    intersectionTransportEquivTo B C (C.flatten R) w hw ψ hψ J'.representation
      A.representation eJ'
  let Q' := (subgroupEqualityFunctor _ _ hR).obj Q
  have eQ' : Q'.representation.Equiv (τ.comp e.symm.toMonoidHom) :=
    subgroupEqualityEquivOf _ _ hR Q τ e.symm.toMonoidHom eQ
  change (T.normalizedRefinedInduced C R Q'.representation).Equiv _
  exact normalizedRefinedInducedCongr T C R eQ'

end Piece

section Factors

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- Transporting the smooth object of a supercuspidal representation along an
equality of ranks gives a supercuspidal representation. -/
theorem supercuspidalProperty_cast {a b : ℕ} (h : a = b)
    (X : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := a)) :
    letI := T.topology
    supercuspidalProperty (F := F.Carrier) (n := b)
      (h ▸ X.obj : SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)) := by
  subst h
  exact X.property

/-- A supercuspidal representation transported along an equality of ranks. -/
def castSupercuspidal {a b : ℕ} (h : a = b)
    (X : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := a)) :
    letI := T.topology
    SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := b) :=
  letI := T.topology
  ⟨(h ▸ X.obj : SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier)),
    supercuspidalProperty_cast T h X⟩

/-- The cuspidal datum of a rank-transported supercuspidal representation is the
cuspidal datum of the original one. -/
theorem cuspidalDatum_castSupercuspidal {a b : ℕ} (h : a = b) (ha : 0 < a) (hb : 0 < b)
    (X : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := a)) :
    letI := T.topology
    (⟨b, hb, (castSupercuspidal T h X).isoClass⟩ : PadicField.TopologicalData.CuspidalDatum.{uV, uF} T) =
      ⟨a, ha, X.isoClass⟩ := by
  subst h
  rfl

variable {n : ℕ} (C : BlockShape n) (R : BlockRefinement C)

/-- The supercuspidal factor of a flattened block, read as a representation of its
inner block. -/
def innerFactor
    (X : letI := T.topology
      ∀ k : Fin (C.flatten R).length,
        SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (C.flatten R).size k))
    (i : Fin C.length) (j : Fin (R i).length) :
    letI := T.topology
    SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (R i).size j) :=
  castSupercuspidal T (C.flatten_size_flattenBlockEquiv R ⟨i, j⟩)
    (X (C.flattenBlockEquiv R ⟨i, j⟩))

/-- The flattened product coordinates of a refined Levi element are its block
coordinates. -/
theorem flattenedLeviProductEquiv_flattenedLeviEquiv_symm
    (m : refinedLevi F.Carrier C R) :
    flattenedLeviProductEquiv F.Carrier C R ((flattenedLeviEquiv F.Carrier C R).symm m) =
      (refinedLeviEquiv F.Carrier C R).symm m := by
  rw [flattenedLeviEquiv, MulEquiv.symm_trans_apply, MulEquiv.apply_symm_apply]

/-- A factorization in flattened product coordinates gives the inducing
representation of the refined induction tensor comparison. -/
def inducingEquiv {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {σ : Representation ℂ ((C.flatten R).Levi F.Carrier) V}
    {A : Parabolic.RefinedInductionTensor.Factors.{uF, uV} F T C R}
    (E : letI := T.topology
      σ.Equiv ((FiniteTensor.external fun i => (A i).representation).comp
        (flattenedLeviProductEquiv F.Carrier C R).toMonoidHom)) :
    Representation.Equiv (σ.comp (flattenedLeviEquiv F.Carrier C R).symm.toMonoidHom)
      (Parabolic.RefinedInductionTensor.inducingRepresentation F T C R A) :=
  Representation.Equiv.mk E.toLinearEquiv fun m => by
    let := T.topology
    have := E.isIntertwining' ((flattenedLeviEquiv F.Carrier C R).symm m)
    simpa only [Parabolic.RefinedInductionTensor.inducingRepresentation,
      MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      flattenedLeviProductEquiv_flattenedLeviEquiv_symm] using this

/-- An irreducible cuspidal representation of a flattened Levi is the block tensor of
supercuspidal representations of its blocks; regrouped over the coarse blocks, its
pullback to the refined Levi is the inducing representation of the inner external
tensor products. -/
theorem exists_inner_factors (hn : 0 < n) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ ((C.flatten R).Levi F.Carrier) V) (hσ : σ.IsIrreducible)
    (hc : letI := T.topology; IsLeviCuspidal (C.flatten R) σ) :
    letI := T.topology
    ∃ X : ∀ k : Fin (C.flatten R).length,
        SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (C.flatten R).size k),
      Nonempty (σ.Equiv ((C.flatten R).blockTensor (fun k => (X k).obj.representation))) ∧
      Nonempty (Representation.Equiv (σ.comp (flattenedLeviEquiv F.Carrier C R).symm.toMonoidHom)
        (Parabolic.RefinedInductionTensor.inducingRepresentation F T C R
          (fun i => FiniteTensor.externalSmoothObject
            (fun j => (innerFactor T C R X i j).obj)))) := by
  let := T.topology
  obtain ⟨X, ⟨eX⟩⟩ := padicLeviCuspidalFactorization.{uF, uV, uV} p F T n hn (C.flatten R)
    (SmoothRep.of σ hc.1.1) hσ hc
  refine ⟨X, ⟨eX⟩, ⟨inducingEquiv T C R ?_⟩⟩
  exact eX.trans (FiniteTensor.flattenedTensorRegroupEquiv F T C R (fun k => (X k).obj))

end Factors

section TensorFactor

open Function

/-- A nonzero linear map out of an external tensor product, equivariant along a map
into the product group which is trivial away from one coordinate, gives a nonzero
equivariant linear map out of that coordinate's factor. -/
theorem exists_factor_map {ι : Type*} [DecidableEq ι] {H : ι → Type*} [∀ i, Group (H i)]
    {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (π : ∀ i, Representation ℂ (H i) (V i)) (i₀ : ι)
    {K : Type*} [Monoid K] (κ : K → ∀ i, H i) (hκ : ∀ g j, j ≠ i₀ → κ g j = 1)
    {W : Type*} [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ K W)
    (ψ : PiTensorProduct ℂ V →ₗ[ℂ] W) (hψ : ψ ≠ 0)
    (heq : ∀ g x, ψ (FiniteTensor.external π (κ g) x) = τ g (ψ x)) :
    ∃ χ : V i₀ →ₗ[ℂ] W, χ ≠ 0 ∧ ∀ g v, χ (π i₀ (κ g i₀) v) = τ g (χ v) := by
  obtain ⟨f, hf⟩ : ∃ f : ∀ i, V i, ψ (PiTensorProduct.tprod ℂ f) ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hψ (PiTensorProduct.ext (MultilinearMap.ext fun f => by simpa using hall f))
  refine ⟨(ψ.compMultilinearMap (PiTensorProduct.tprod ℂ)).toLinearMap f i₀, ?_, ?_⟩
  · intro hz
    apply hf
    have := LinearMap.congr_fun hz (f i₀)
    simpa [MultilinearMap.toLinearMap_apply] using this
  · intro g v
    simp only [MultilinearMap.toLinearMap_apply, LinearMap.compMultilinearMap_apply]
    rw [← heq, FiniteTensor.external_tprod]
    congr 2
    funext j
    by_cases hj : j = i₀
    · subst hj
      simp
    · rw [update_of_ne hj, update_of_ne hj, hκ g j hj, map_one, Module.End.one_apply]

/-- A nonzero equivariant linear map onto an irreducible smooth representation makes
it a quotient. -/
theorem isQuotient_of_ne_zero {G : Type uF} [Group G] [TopologicalSpace G]
    {P Q : SmoothRep.{0, uF, uV} ℂ G} (hQ : Q.IsIrreducible) (χ : P →ₗ[ℂ] Q)
    (hχ : χ ≠ 0) (heq : ∀ g v, χ (P.representation g v) = Q.representation g (χ v)) :
    SmoothRep.IsQuotient Q P := by
  let f : P.representation.IntertwiningMap Q.representation :=
    χ.intertwiningMap_of_isIntertwiningMap P.representation Q.representation heq
  have : Q.representation.IsIrreducible := hQ
  refine ⟨SmoothRep.ofHom f, ?_⟩
  rcases Representation.IsIrreducible.surjective_or_eq_zero f with hs | hz
  · exact hs
  · exact absurd (congrArg Representation.IntertwiningMap.toLinearMap hz) hχ

end TensorFactor

section Core

/-- A subfamily along an injective reindexing gives a submultiset. -/
theorem ofFn_comp_le {α : Type*} {l m : ℕ} (g : Fin m → α) (f : Fin l → Fin m)
    (hf : Function.Injective f) :
    (List.ofFn (g ∘ f) : Multiset α) ≤ List.ofFn g := by
  have hsub : (List.ofFn f : Multiset (Fin m)) ≤ (List.finRange m : Multiset (Fin m)) :=
    Multiset.coe_le.mpr ((List.nodup_ofFn.mpr hf).subperm fun x _ => List.mem_finRange x)
  have h := Multiset.map_le_map (f := g) hsub
  rwa [Multiset.map_coe, Multiset.map_coe, List.map_ofFn, ← List.ofFn_eq_map] at h

/-- Transfer of an equivariant nonzero linear map along an equivalence of
representations. -/
theorem exists_map_of_equiv {G : Type*} [Monoid G] {V₁ V₂ : Type*} [AddCommGroup V₁]
    [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂] {π₁ : Representation ℂ G V₁}
    {π₂ : Representation ℂ G V₂} (E : π₁.Equiv π₂) {H : Type*} [Monoid H] (ι : H → G)
    {W : Type*} [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ H W)
    (ψ : V₁ →ₗ[ℂ] W) (hψ : ψ ≠ 0) (heq : ∀ h v, ψ (π₁ (ι h) v) = τ h (ψ v)) :
    ∃ χ : V₂ →ₗ[ℂ] W, χ ≠ 0 ∧ ∀ h v, χ (π₂ (ι h) v) = τ h (χ v) := by
  refine ⟨ψ.comp E.symm.toLinearMap, ?_, ?_⟩
  · intro hz
    apply hψ
    ext v
    have := LinearMap.congr_fun hz (E v)
    change ψ (E.symm (E v)) = 0 at this
    rwa [Representation.Equiv.symm_apply_apply] at this
  · intro h v
    have hI := LinearMap.congr_fun (E.symm.toIntertwiningMap.isIntertwining' (ι h)) v
    change E.symm (π₂ (ι h) v) = π₁ (ι h) (E.symm v) at hI
    change ψ (E.symm (π₂ (ι h) v)) = τ h (ψ (E.symm v))
    rw [hI]
    exact heq h _

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- A nonzero map out of the external tensor product of the two induced blocks of a
refinement of `(a, b)`, equivariant for the first block, makes an irreducible
representation of `GL_a` a quotient of the first induced block. -/
theorem isQuotient_first_block {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (R : BlockRefinement (Shahidi.twoBlocks a b ha hb))
    (A : Parabolic.RefinedInductionTensor.Factors.{uF, uV} F T
      (Shahidi.twoBlocks a b ha hb) R)
    (τ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
    (hτ : letI := T.topology; τ.IsIrreducible)
    (ψ : letI := T.topology
      PiTensorProduct ℂ (Parabolic.RefinedInductionTensor.BlockFunctions F T
        (Shahidi.twoBlocks a b ha hb) R A) →ₗ[ℂ] τ)
    (hψ : ψ ≠ 0)
    (heq : letI := T.topology
      ∀ g x, ψ (FiniteTensor.external
        (Parabolic.RefinedInductionTensor.blockRepresentations F T
          (Shahidi.twoBlocks a b ha hb) R A)
        ((Shahidi.twoBlockLeviEquiv ha hb F.Carrier).symm (g, 1)) x) =
      τ.representation g (ψ x)) :
    letI := T.topology
    SmoothRep.IsQuotient τ ((T.normalizedParabolicInductionFunctor (R 0)).obj (A 0)) := by
  let := T.topology
  obtain ⟨χ, hχ, hχeq⟩ := exists_factor_map
    (Parabolic.RefinedInductionTensor.blockRepresentations F T
      (Shahidi.twoBlocks a b ha hb) R A) 0
    (fun g => (Shahidi.twoBlockLeviEquiv ha hb F.Carrier).symm (g, 1))
    (fun g j hj => by
      fin_cases j
      · exact (hj rfl).elim
      · rfl)
    τ.representation ψ hψ heq
  exact isQuotient_of_ne_zero (Q := τ) hτ χ hχ fun g v => hχeq g v

/-- In a geometric piece with full source refinement, a nonzero map equivariant for
the first block of `(a, b)` makes an irreducible representation of `GL_a` a quotient
of the first induced block of any factorization of the transported inducing
representation. -/
theorem full_piece_quotient {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (B : BlockShape (a + b)) (w : Equiv.Perm (Fin (a + b)))
    (S : BlockRefinement B) (R : BlockRefinement (Shahidi.twoBlocks a b ha hb))
    (hS : sourceLevi F.Carrier B (Shahidi.twoBlocks a b ha hb) w = refinedLevi F.Carrier B S)
    (hR : sourceLevi F.Carrier (Shahidi.twoBlocks a b ha hb) B w⁻¹ =
      refinedLevi F.Carrier (Shahidi.twoBlocks a b ha hb) R)
    (hfull : refinedLevi F.Carrier B S = ⊤)
    (hw : ConjugatesLevi (F := F.Carrier) B ((Shahidi.twoBlocks a b ha hb).flatten R) w)
    (P0 : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier))
    (A : Parabolic.RefinedInductionTensor.Factors.{uF, uV} F T
      (Shahidi.twoBlocks a b ha hb) R)
    (eI : letI := T.topology
      Representation.Equiv
      ((transport B ((Shahidi.twoBlocks a b ha hb).flatten R) w hw P0.representation).comp
        (flattenedLeviEquiv F.Carrier (Shahidi.twoBlocks a b ha hb) R).symm.toMonoidHom)
      (Parabolic.RefinedInductionTensor.inducingRepresentation F T
        (Shahidi.twoBlocks a b ha hb) R A))
    (τ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
    (hτ : letI := T.topology; τ.IsIrreducible)
    (ψ : letI := T.topology
      ((geometricPieceFunctor T B (Shahidi.twoBlocks a b ha hb) w S R hS hR).obj P0) →ₗ[ℂ] τ)
    (hψ : ψ ≠ 0)
    (heq : letI := T.topology
      ∀ g v, ψ (((geometricPieceFunctor T B (Shahidi.twoBlocks a b ha hb) w S R hS hR).obj
        P0).ρ ((Shahidi.twoBlockLeviEquiv ha hb F.Carrier).symm (g, 1)) v) =
      τ.representation g (ψ v)) :
    letI := T.topology
    SmoothRep.IsQuotient τ ((T.normalizedParabolicInductionFunctor (R 0)).obj (A 0)) := by
  let := T.topology
  let EP := fullSourcePieceEquiv T B _ w S R hS hR hfull hw P0
  let EF := normalizedRefinedInducedCongr T _ R eI
  obtain ⟨⟨ET, -⟩⟩ := Parabolic.refinedInductionTensor p F T (a + b) _ R A
  obtain ⟨χ, hχ, hχeq⟩ := exists_map_of_equiv (EP.trans (EF.trans ET))
    (fun g => (Shahidi.twoBlockLeviEquiv ha hb F.Carrier).symm (g, 1)) τ.representation
    ψ hψ heq
  exact isQuotient_first_block T ha hb R A τ hτ χ hχ hχeq

open PadicField.TopologicalData in
/-- The cuspidal product of a family of supercuspidal representations indexed by the
blocks of a shape is the normalized parabolic induction of their external tensor
product; so a quotient of the latter is a subquotient of the former. -/
theorem isSubquotient_cuspidalProductInduced {m : ℕ} (D : BlockShape m)
    (X : letI := T.topology
      ∀ j, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := D.size j))
    (τ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier))
    (hq : letI := T.topology
      SmoothRep.IsQuotient τ ((T.normalizedParabolicInductionFunctor D).obj
        (FiniteTensor.externalSmoothObject fun j => (X j).obj))) :
    letI := T.topology
    SmoothRep.IsSubquotient τ (T.cuspidalProductInduced
      (fun j => (⟨D.size j, D.positive j, (X j).isoClass⟩ : CuspidalDatum.{uV, uF} T))
      D.sum_eq X) := by
  let := T.topology
  obtain ⟨l, size, pos, sum⟩ := D
  exact hq.isSubquotient

open PadicField.TopologicalData in
/-- In a geometric piece of the `(a, b)` Jacquet module of a supercuspidal product
with full source refinement, an irreducible representation of `GL_a` receiving a
nonzero first-block-equivariant map is a constituent of a product of a submultiset of
the supercuspidal data. -/
theorem full_piece_support {a b k : ℕ} (ha : 0 < a) (hb : 0 < b)
    (ρ : Fin k → CuspidalDatum.{uV, uF} T) (h : ∑ i, (ρ i).rank = a + b)
    (A : letI := T.topology
      ∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρ i).rank))
    (hA : ∀ i, (ρ i).IsRepresentedBy (A i))
    (τ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
    (hτ : letI := T.topology; τ.IsIrreducible)
    (w : Equiv.Perm (Fin (a + b))) (S : BlockRefinement (T.cuspidalShape ρ h))
    (R : BlockRefinement (Shahidi.twoBlocks a b ha hb))
    (hS : sourceLevi F.Carrier (T.cuspidalShape ρ h) (Shahidi.twoBlocks a b ha hb) w =
      refinedLevi F.Carrier (T.cuspidalShape ρ h) S)
    (hR : sourceLevi F.Carrier (Shahidi.twoBlocks a b ha hb) (T.cuspidalShape ρ h) w⁻¹ =
      refinedLevi F.Carrier (Shahidi.twoBlocks a b ha hb) R)
    (hfull : refinedLevi F.Carrier (T.cuspidalShape ρ h) S = ⊤)
    (ψ : letI := T.topology
      ((geometricPieceFunctor T (T.cuspidalShape ρ h) (Shahidi.twoBlocks a b ha hb) w S R
        hS hR).obj (FiniteTensor.externalSmoothObject fun i => (A i).obj)) →ₗ[ℂ] τ)
    (hψ : ψ ≠ 0)
    (heq : letI := T.topology
      ∀ g v, ψ (((geometricPieceFunctor T (T.cuspidalShape ρ h) (Shahidi.twoBlocks a b ha hb)
        w S R hS hR).obj (FiniteTensor.externalSmoothObject fun i => (A i).obj)).ρ
          ((Shahidi.twoBlockLeviEquiv ha hb F.Carrier).symm (g, 1)) v) =
        τ.representation g (ψ v)) :
    ∃ (l : ℕ) (ρ'' : Fin l → CuspidalDatum.{uV, uF} T),
      T.IsCuspidalConstituent ρ'' τ ∧
      (List.ofFn ρ'' : Multiset (CuspidalDatum.{uV, uF} T)) ≤ List.ofFn ρ := by
  classical
  let := T.topology
  have : IsTopologicalRing F.Carrier := by
    let := T.valuativeRel
    have := T.localField
    infer_instance
  have hn : 0 < a + b := by omega
  obtain ⟨hirr, hc⟩ := glCuspidalTensor p F T (a + b) hn (T.cuspidalShape ρ h) A
  have hsrc : sourceLevi F.Carrier (T.cuspidalShape ρ h) (Shahidi.twoBlocks a b ha hb) w = ⊤ :=
    hS.trans hfull
  have hw := conjugatesLevi_flatten_of_source_top (F := F.Carrier) (T.cuspidalShape ρ h)
    (Shahidi.twoBlocks a b ha hb) R w hsrc hR
  obtain ⟨X, ⟨eX⟩, ⟨eI⟩⟩ := exists_inner_factors T (Shahidi.twoBlocks a b ha hb) R hn
    (transport _ _ w hw (FiniteTensor.external fun i => (A i).obj.representation))
    ((isIrreducible_transport w hw _).mpr hirr)
    (isLeviCuspidal_transport_of_conjugatesLevi _ _ w hw _ hc)
  have hquot := full_piece_quotient T ha hb (T.cuspidalShape ρ h) w S R hS hR hfull hw
    (FiniteTensor.externalSmoothObject fun i => (A i).obj)
    (fun i => FiniteTensor.externalSmoothObject fun j =>
      (innerFactor T (Shahidi.twoBlocks a b ha hb) R X i j).obj)
    eI τ hτ ψ hψ heq
  let D := (Shahidi.twoBlocks a b ha hb).flatten R
  let ρ' : Fin D.length → CuspidalDatum.{uV, uF} T :=
    fun j => ⟨D.size j, D.positive j, (X j).isoClass⟩
  have assoc : (List.ofFn ρ : Multiset (CuspidalDatum.{uV, uF} T)) = List.ofFn ρ' :=
    glCuspidalTensorAssociation p F T (a + b) hn k D.length ρ ρ' h D.sum_eq A X hA
      (fun _ => rfl) ⟨w, hw, ⟨eX⟩⟩
  let ρ'' : Fin (R 0).length → CuspidalDatum.{uV, uF} T := fun j =>
    ⟨(R 0).size j, (R 0).positive j,
      (innerFactor T (Shahidi.twoBlocks a b ha hb) R X 0 j).isoClass⟩
  refine ⟨(R 0).length, ρ'', ⟨(R 0).sum_eq,
    fun j => innerFactor T (Shahidi.twoBlocks a b ha hb) R X 0 j,
    fun _ => rfl, hτ,
    isSubquotient_cuspidalProductInduced T (R 0)
      (innerFactor T (Shahidi.twoBlocks a b ha hb) R X 0) τ hquot⟩, ?_⟩
  have hρ'' : ρ'' = ρ' ∘ fun j => (Shahidi.twoBlocks a b ha hb).flattenBlockEquiv R ⟨0, j⟩ := by
    funext j
    exact cuspidalDatum_castSupercuspidal T _ _ _ _
  rw [hρ'', assoc]
  exact ofFn_comp_le ρ' _ fun j j' hjj' => by
    have := ((Shahidi.twoBlocks a b ha hb).flattenBlockEquiv R).injective hjj'
    simpa using this

open PadicField.TopologicalData in
/-- An irreducible representation of `GL_a` receiving a nonzero map from the
`(a, b)` Jacquet module of a supercuspidal product, equivariant for the first block,
is a constituent of a product of a submultiset of the supercuspidal data. -/
theorem jacquet_quotient_support {a b k : ℕ} (ha : 0 < a) (hb : 0 < b)
    (ρ : Fin k → CuspidalDatum.{uV, uF} T) (h : ∑ i, (ρ i).rank = a + b)
    (A : letI := T.topology
      ∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρ i).rank))
    (hA : ∀ i, (ρ i).IsRepresentedBy (A i))
    (τ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
    (hτ : letI := T.topology; τ.IsIrreducible)
    (φ : letI := T.topology
      ((T.normalizedJacquetFunctor (Shahidi.twoBlocks a b ha hb)).obj
        (T.cuspidalProductInduced ρ h A)) →ₗ[ℂ] τ)
    (hφ : φ ≠ 0)
    (heq : letI := T.topology
      ∀ g v, φ (((T.normalizedJacquetFunctor (Shahidi.twoBlocks a b ha hb)).obj
        (T.cuspidalProductInduced ρ h A)).representation
          ((Shahidi.twoBlockLeviEquiv ha hb F.Carrier).symm (g, 1)) v) =
        τ.representation g (φ v)) :
    ∃ (l : ℕ) (ρ'' : Fin l → CuspidalDatum.{uV, uF} T),
      T.IsCuspidalConstituent ρ'' τ ∧
      (List.ofFn ρ'' : Multiset (CuspidalDatum.{uV, uF} T)) ≤ List.ofFn ρ := by
  let := T.topology
  have hn : 0 < a + b := by omega
  obtain ⟨-, hc⟩ := glCuspidalTensor p F T (a + b) hn (T.cuspidalShape ρ h) A
  obtain ⟨S, R, hS, hR, m, e, perm, s, hs⟩ := Geometric.padicGeometricLemma.{uF, uV} p F T
    (a + b) hn (T.cuspidalShape ρ h) (Shahidi.twoBlocks a b ha hb)
  obtain ⟨i, ψ, hψ, hψeq⟩ := exists_graded_map s
    (FiniteTensor.externalSmoothObject fun i => (A i).obj)
    (fun g => (Shahidi.twoBlockLeviEquiv ha hb F.Carrier).symm (g, 1))
    τ.representation φ hφ heq
  obtain ⟨E⟩ := hs i
  let P := (geometricPieceFunctor T (T.cuspidalShape ρ h) (Shahidi.twoBlocks a b ha hb)
    (e (perm i)).val (S (e (perm i))) (R (e (perm i))) (hS (e (perm i))).2.1
    (hR (e (perm i))).2.1).obj (FiniteTensor.externalSmoothObject fun i => (A i).obj)
  have E' : (s.graded i).obj (FiniteTensor.externalSmoothObject fun i => (A i).obj) ≅ P :=
    E.app _
  obtain ⟨ψ', hψ', hψ'eq⟩ := exists_map_of_iso E'
    (fun g => (Shahidi.twoBlockLeviEquiv ha hb F.Carrier).symm (g, 1))
    τ.representation ψ hψ hψeq
  by_cases hP : refinedParabolic F.Carrier (T.cuspidalShape ρ h) (S (e (perm i))) = ⊤
  · exact full_piece_support T ha hb ρ h A hA τ hτ (e (perm i)).val (S (e (perm i)))
      (R (e (perm i))) (hS (e (perm i))).2.1 (hR (e (perm i))).2.1
      (refinedLevi_eq_top_of_refinedParabolic_eq_top _ _ hP) ψ' hψ' hψ'eq
  · exfalso
    have hsub := geometricPieceFunctor_subsingleton_of_proper_source F T _ _ (e (perm i)).val
      (S (e (perm i))) (R (e (perm i))) (hS (e (perm i))).2.1 (hR (e (perm i))).2.1 _ hc.2 hP
    exact hψ' (LinearMap.ext fun v => by
      rw [@Subsingleton.elim _ hsub v 0, map_zero, LinearMap.zero_apply])

end Core

section Derivative

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- A nonzero equivariant map onto an irreducible representation survives a rank
cast, together with irreducibility. -/
theorem exists_rankCast_map {m m' : ℕ} (h : m = m')
    (X : letI := T.topology; SmoothRep.{0, uF, uW} ℂ (GeneralLinear m F.Carrier))
    (τ : letI := T.topology; SmoothRep.{0, uF, uW} ℂ (GeneralLinear m F.Carrier))
    (hτ : letI := T.topology; τ.IsIrreducible)
    (χ : letI := T.topology; X →ₗ[ℂ] τ) (hχ : χ ≠ 0)
    (heq : letI := T.topology
      ∀ g v, χ (X.representation g v) = τ.representation g (χ v)) :
    letI := T.topology
    ((Derivative.generalLinearRankCast.{uF, uW} T h).obj τ).IsIrreducible ∧
    ∃ χ' : (Derivative.generalLinearRankCast.{uF, uW} T h).obj X →ₗ[ℂ]
        (Derivative.generalLinearRankCast.{uF, uW} T h).obj τ,
      χ' ≠ 0 ∧ ∀ g v,
        χ' (((Derivative.generalLinearRankCast.{uF, uW} T h).obj X).representation g v) =
          ((Derivative.generalLinearRankCast.{uF, uW} T h).obj τ).representation g (χ' v) := by
  subst h
  exact ⟨hτ, χ, hχ, heq⟩

open PadicField.TopologicalData in
/-- Cuspidal constituency is unchanged by a rank cast. -/
theorem isCuspidalConstituent_of_rankCast {m m' : ℕ} (h : m = m') {l : ℕ}
    (ρ'' : Fin l → CuspidalDatum.{uV, uF} T)
    (τ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier))
    (hc : T.IsCuspidalConstituent ρ''
      ((Derivative.generalLinearRankCast.{uF, max uF uV} T h).obj τ)) :
    T.IsCuspidalConstituent ρ'' τ := by
  subst h
  exact hc

open PadicField.TopologicalData in
/-- An irreducible representation of `GL_(n-k)` receiving a nonzero equivariant map
from the order-`k` derivative of a supercuspidal product, with `0 < k < n`, is a
constituent of a product of a submultiset of the supercuspidal data. -/
theorem derivative_quotient_support
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    {n k : ℕ} (hk : k ≤ n) (hk0 : 0 < k) (hkn : k < n) {r : ℕ}
    (ρ : Fin r → CuspidalDatum.{uV, uF} T) (h : ∑ i, (ρ i).rank = n)
    (A : letI := T.topology
      ∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρ i).rank))
    (hA : ∀ i, (ρ i).IsRepresentedBy (A i))
    (τ : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (n - k) F.Carrier))
    (hτ : letI := T.topology; τ.IsIrreducible)
    (χ : letI := T.topology
      ((Derivative.generalLinearDerivative.{uF, max uF uV} T ψ n k hk).obj
        (T.cuspidalProductInduced ρ h A)) →ₗ[ℂ] τ)
    (hχ : χ ≠ 0)
    (heq : letI := T.topology
      ∀ g v, χ (((Derivative.generalLinearDerivative.{uF, max uF uV} T ψ n k hk).obj
        (T.cuspidalProductInduced ρ h A)).representation g v) = τ.representation g (χ v)) :
    ∃ (l : ℕ) (ρ'' : Fin l → CuspidalDatum.{uV, uF} T),
      T.IsCuspidalConstituent ρ'' τ ∧
      (List.ofFn ρ'' : Multiset (CuspidalDatum.{uV, uF} T)) ≤ List.ofFn ρ := by
  let := T.topology
  obtain ⟨a, rfl⟩ : ∃ a, n = a + k := ⟨n - k, by omega⟩
  have ha : 0 < a := by omega
  have hc : a + k - k = a := Nat.add_sub_cancel a k
  obtain ⟨hτ', χ', hχ', heq'⟩ := exists_rankCast_map T hc _ τ hτ χ hχ heq
  obtain ⟨E⟩ := Derivative.partialDerivativeJacquetComparison.{uF, max uF uV} F T ψ a k ha hk0
  obtain ⟨χ'', hχ'', heq''⟩ := exists_map_of_equiv
    (SmoothRep.equivOfIso (E.app (T.cuspidalProductInduced ρ h A))) id _ χ' hχ' heq'
  let J := (Derivative.positiveTwoBlockNormalizedJacquet.{uF, max uF uV} T a k ha hk0).obj
    (T.cuspidalProductInduced ρ h A)
  let φ : ((T.normalizedJacquetFunctor (Shahidi.twoBlocks a k ha hk0)).obj
      (T.cuspidalProductInduced ρ h A)) →ₗ[ℂ]
      (Derivative.generalLinearRankCast.{uF, max uF uV} T hc).obj τ :=
    χ''.comp (Derivative.partialDerivativeMk T ψ a k J)
  have hφ : φ ≠ 0 := by
    intro hz
    apply hχ''
    ext x
    obtain ⟨v, rfl⟩ := Derivative.partialDerivativeMk_surjective T ψ a k J x
    exact LinearMap.congr_fun hz v
  have hφeq : ∀ g v, φ (((T.normalizedJacquetFunctor (Shahidi.twoBlocks a k ha hk0)).obj
      (T.cuspidalProductInduced ρ h A)).representation
        ((Shahidi.twoBlockLeviEquiv ha hk0 F.Carrier).symm (g, 1)) v) =
      ((Derivative.generalLinearRankCast.{uF, max uF uV} T hc).obj τ).representation g
        (φ v) := by
    intro g v
    exact (congrArg χ'' (Derivative.partialDerivative_action_mk T ψ a k J g v)).symm.trans
      (heq'' g _)
  obtain ⟨l, ρ'', hcon, hle⟩ := jacquet_quotient_support T ha hk0 ρ h A hA _ hτ' φ hφ hφeq
  exact ⟨l, ρ'', isCuspidalConstituent_of_rankCast T hc ρ'' τ hcon, hle⟩

end Derivative

end Langlands.Classification.CuspidalProductDerivativeQuotientSupport
