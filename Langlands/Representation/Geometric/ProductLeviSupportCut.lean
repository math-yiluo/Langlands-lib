import Langlands.Representation.Geometric.OpenOrbitCut
import Langlands.Representation.Geometric.ProductLeviSupportKernel
import Langlands.Representation.Geometric.BruhatDescent
import Langlands.Group.GL.RefinementCoordinates
import Langlands.Representation.Filtration.QuotientTail

noncomputable section
open CategoryTheory
namespace Langlands.Geometric
open GeneralLinear Parabolic
universe uG uK uF uV

section SubgroupLocus
variable {G : Type uG} [Group G]

/-- The image of an intermediate subgroup in the actual left coset space. -/
def subgroupLocus (P K : Subgroup G) : Set (Induction.LeftQuotient P) :=
  Induction.quotientMap P '' (K : Set G)

theorem quotientMap_mem_subgroupLocus_iff (P K : Subgroup G) (hPK : P ≤ K) (g : G) :
    Induction.quotientMap P g ∈ subgroupLocus P K ↔ g ∈ K := by
  constructor
  · rintro ⟨k, hk, hkg⟩
    have hp : g * k⁻¹ ∈ P := QuotientGroup.rightRel_apply.mp (Quotient.exact hkg)
    simpa using K.mul_mem (hPK hp) hk
  · intro hg
    exact ⟨g, hg, rfl⟩

variable [TopologicalSpace G]
theorem isClosed_subgroupLocus (P K : Subgroup G) (hPK : P ≤ K)
    (hK : IsClosed (K : Set G)) : IsClosed (subgroupLocus P K) := by
  apply (isQuotientMap_quotient_mk' (s := QuotientGroup.rightRel P)).isCoinducing.isClosed_preimage.mp
  change IsClosed (Induction.quotientMap P ⁻¹' subgroupLocus P K)
  convert hK using 1
  ext g
  exact quotientMap_mem_subgroupLocus_iff P K hPK g

omit [TopologicalSpace G] in
theorem cosetOrbit_mem_subgroupLocus_iff (P Q K : Subgroup G)
    (hPK : P ≤ K) (hQK : Q ≤ K) (w : G) (x : Induction.LeftQuotient P)
    (hx : x ∈ cosetOrbit P Q w) : x ∈ subgroupLocus P K ↔ w ∈ K := by
  obtain ⟨q, rfl⟩ := hx
  rw [quotientMap_mem_subgroupLocus_iff P K hPK]
  constructor
  · intro h
    have h' : w⁻¹ ∈ K := by simpa [mul_assoc] using K.mul_mem h (K.inv_mem (hQK q.property))
    exact K.inv_mem_iff.mp h'
  · intro h
    exact K.mul_mem (K.inv_mem h) (hQK q.property)
end SubgroupLocus

section Matrices
variable (K : Type uK) [CommRing K] {n : ℕ} (B : BlockShape n)

theorem flattenedParabolic_le (Q : BlockRefinement B) :
    (B.flatten Q).parabolic K ≤ B.parabolic K := by
  have he : composedParabolic K B Q = (B.flatten Q).parabolic K :=
    (B.flatten Q).composedParabolic_eq_of_coordinates B Q (B.flattenBlockEquiv Q)
      (fun a => (B.flatten_size_flattenBlockEquiv Q a).symm) K
      (fun i k x => B.index_index_eq_flatten Q ⟨i, k⟩ x)
  rw [← he]
  intro g hg
  exact ((mem_leviPreimage_iff K B _ g).mp hg).1

variable [Nontrivial K]
private theorem blockIndex_le_of_permutation_mem (w : Equiv.Perm (Fin n))
    (h : permutation n K w ∈ B.parabolic K) (a : Fin n) :
    blockIndex B (w a) ≤ blockIndex B a := by
  by_contra hlt
  have hz := (B.mem_parabolic_iff K _).mp h
    (blockIndex B (w a)) (blockIndex B a)
    (B.indexEquiv.symm (w a)).2 (B.indexEquiv.symm a).2 (lt_of_not_ge hlt)
  have hind (x : Fin n) : B.index (blockIndex B x) (B.indexEquiv.symm x).2 = x :=
    B.indexEquiv.apply_symm_apply x
  simp only [hind, permutation_entry, ite_true] at hz
  exact one_ne_zero hz

/-- A permutation matrix is in a standard parabolic exactly when its permutation
preserves every block. -/
theorem permutation_mem_parabolic_iff (w : Equiv.Perm (Fin n)) :
    permutation n K w ∈ B.parabolic K ↔ w ∈ blockWeyl B := by
  constructor
  · intro h a
    apply le_antisymm
    · exact blockIndex_le_of_permutation_mem K B w h a
    · have hi : permutation n K w⁻¹ ∈ B.parabolic K := by
        rw [map_inv]
        exact (B.parabolic K).inv_mem h
      simpa using blockIndex_le_of_permutation_mem K B w⁻¹ hi (w a)
  · exact permutation_mem_parabolic_of_mem_blockWeyl K B
end Matrices

section Padic
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n)

/-- The closed coarse parabolic image inside the fine left coset space. -/
def coarseParabolicLocus (Q : BlockRefinement B) :
    Set (Induction.LeftQuotient ((B.flatten Q).parabolic F.Carrier)) :=
  subgroupLocus ((B.flatten Q).parabolic F.Carrier) (B.parabolic F.Carrier)

theorem quotientMap_mem_coarseParabolicLocus_iff (Q : BlockRefinement B)
    (g : GeneralLinear n F.Carrier) :
    Induction.quotientMap ((B.flatten Q).parabolic F.Carrier) g ∈
      coarseParabolicLocus (F := F) B Q ↔ g ∈ B.parabolic F.Carrier :=
  quotientMap_mem_subgroupLocus_iff _ _ (flattenedParabolic_le F.Carrier B Q) g

/-- The closed coarse subset can be placed at the end of any actual fine
ordered double-coset cover. -/
theorem exists_productLeviSupportCut (Q S : BlockRefinement B) {m : ℕ} :
    letI := T.topology
    ∀ s : OrderedDoubleCosets ((B.flatten Q).parabolic F.Carrier)
      ((B.flatten S).parabolic F.Carrier) m,
      ∃ (a b : ℕ) (e : Fin (a + b) ≃ Fin m)
        (t : OrderedDoubleCosets ((B.flatten Q).parabolic F.Carrier)
          ((B.flatten S).parabolic F.Carrier) (a + b)),
        (∀ i, t.representative i = s.representative (e i)) ∧
        t.initialOrbits ⟨a, by omega⟩ = (coarseParabolicLocus (F := F) B Q)ᶜ := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  intro s
  apply s.exists_openCut ((coarseParabolicLocus (F := F) B Q)ᶜ)
    ((isClosed_subgroupLocus _ _ (flattenedParabolic_le F.Carrier B Q)
      (B.isClosed_parabolic F.Carrier)).isOpen_compl)
    (fun i => s.representative i ∉ B.parabolic F.Carrier)
  intro i x hx
  exact not_congr (cosetOrbit_mem_subgroupLocus_iff _ _ _
    (flattenedParabolic_le F.Carrier B Q) (flattenedParabolic_le F.Carrier B S)
    (s.representative i) x hx)

/-- The support image at the coarse-complement cut is exactly the kernel of
the actual natural product-Levi quotient. -/
theorem productLeviSupportCut_ker (Q S : BlockRefinement B) {a b : ℕ} :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ (s : OrderedDoubleCosets ((B.flatten Q).parabolic F.Carrier)
        ((B.flatten S).parabolic F.Carrier) (a + b)),
      s.initialOrbits ⟨a, by omega⟩ = (coarseParabolicLocus (F := F) B Q)ᶜ →
      ∀ (A : SmoothRep.{0, uF, uV} ℂ ((B.flatten Q).Levi F.Carrier))
        (v : (jacquetInductionFunctor T (B.flatten Q) (B.flatten S)).obj A),
        v ∈ ((parabolicJacquetSupportFiltration T (B.flatten Q) (B.flatten S) s).step
          (RepFunctorFiltration.tailIndex a b 0)).obj A ↔
          ((productLeviQuotientMap T B Q S).app A).hom v = 0 := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro s hcut A v
  have hraw :
      (((parabolicInductionSupportFiltration T (B.flatten Q) (B.flatten S) s).step
        (RepFunctorFiltration.tailIndex a b 0)).obj A).toSubmodule =
      LinearMap.ker (productLeviRestrictionMap T B Q A) := by
    apply SetLike.ext
    intro f
    change (∀ g : GeneralLinear n F.Carrier, Induction.eval _ _ f g ≠ 0 →
      Induction.quotientMap ((B.flatten Q).parabolic F.Carrier) g ∈
        s.initialOrbits (RepFunctorFiltration.tailIndex a b 0)) ↔
      productLeviRestrictionMap T B Q A f = 0
    rw [productLeviRestrictionMap_eq_zero_iff]
    have hi : RepFunctorFiltration.tailIndex a b 0 = (⟨a, by omega⟩ : Fin (a + b + 1)) :=
      Fin.ext (Nat.add_zero a)
    rw [hi, hcut]
    constructor
    · intro hf g
      by_contra hfg
      exact hf g.val hfg ((quotientMap_mem_coarseParabolicLocus_iff B Q g.val).mpr g.property)
    · intro hf g hfg hg
      exact hfg (hf ⟨g, (quotientMap_mem_coarseParabolicLocus_iff B Q g).mp hg⟩)
  change v ∈ Submodule.map _ _ ↔ _
  rw [hraw]
  erw [← productLeviQuotientMap_ker T B Q S A]
  rfl
end Padic
end Langlands.Geometric
