import Langlands.Representation.Exponents.WeylBranchPiecesSubquotient
import Langlands.Representation.Jacquet.CharacterTwistEquiv
import Langlands.Representation.Parabolic.RefinedLeviRealTwistProof
import Langlands.Representation.Parabolic.OppositeRefinementTransitivityProof
import Langlands.Representation.Classification.UnitaryWeylRigidityProof
import Langlands.Representation.Classification.FineTwistRegularityProof
import Langlands.Representation.Classification.ProductLeviMinimalIndex
import Langlands.Representation.Twist.LeviComplexPowerConjugationProof
import Langlands.Representation.Twist.LeviComplexPowerRefinementProof
import Langlands.Representation.Twist.SubquotientProof
import Langlands.Representation.Twist.AdmissibilityProof
import Langlands.Representation.Twist.PullbackProof
import Langlands.Representation.CuspidalSupport.MinimalWeylTransportProof
import Langlands.Representation.CuspidalSupport.AssociationReduction
import Langlands.Representation.Smooth.Transfer.SubquotientProof
import Langlands.Representation.Geometric.WeylMinimalRepresentativeProof
import Langlands.Representation.Geometric.WeylUniquenessProof

/-!
# Conditional assembly of the supported excess-multiplicity Weyl branch

The target `GLSupportedRegularMultiplicityBranchObstructionStatement` follows
from the four Weyl-piece interfaces of `WeylBranchPiecesStatement`.
-/

noncomputable section

namespace Langlands

open GeneralLinear Geometric
open RelativeJacquetMultiplicity RelativeRegularComparison

namespace WeylBranchPieces

section Combinatorics

variable {n : ℕ}

/-- Order preservation on every block, in coordinate form. -/
theorem strictMono_blocks_iff (E : BlockShape n) (y : Equiv.Perm (Fin n)) :
    (∀ j, StrictMono (fun a : Fin (E.size j) => y (E.index j a))) ↔
      ∀ a b, blockIndex E a = blockIndex E b → a < b → y a < y b := by
  constructor
  · intro h a b hab hlt
    obtain ⟨a', ha'⟩ := exists_index_of_blockIndex_eq E (rfl : blockIndex E a = blockIndex E a)
    obtain ⟨b', hb'⟩ := exists_index_of_blockIndex_eq E hab.symm
    rw [← ha', ← hb'] at hlt ⊢
    exact h _ ((index_strictMono E _).lt_iff_lt.mp hlt)
  · intro h j a b hab
    exact h _ _ (by simp only [blockIndex_index]) (index_strictMono E j hab)

/-- The minimality conditions are symmetric under inversion. -/
theorem IsMinimalRepresentative.inv {E E' : BlockShape n} {w : Equiv.Perm (Fin n)}
    (h : IsMinimalRepresentative E E' w) : IsMinimalRepresentative E' E w⁻¹ :=
  ⟨h.2, h.1⟩

/-- Minimality persists when the source shape is refined. -/
theorem IsMinimalRepresentative.flatten_left {B C : BlockShape n} (S : BlockRefinement B)
    {w : Equiv.Perm (Fin n)} (h : IsMinimalRepresentative B C w) :
    IsMinimalRepresentative (B.flatten S) C w := by
  refine ⟨(strictMono_blocks_iff _ w).mpr fun a b hab hlt => ?_, h.2⟩
  have hB : blockIndex B a = blockIndex B b := by
    rw [ProductLeviMinimalIndex.blockIndex_eq_flatten B S a,
      ProductLeviMinimalIndex.blockIndex_eq_flatten B S b, hab]
  exact (strictMono_blocks_iff B w).mp h.1 a b hB hlt

/-- A coarse minimal representative followed by a coarse-Weyl minimal
representative of the middle shape is minimal for the middle shape. -/
theorem isMinimalRepresentative_mul {F : Type*} [Field F] {B : BlockShape n}
    (Q S S' : BlockRefinement B) {x g : Equiv.Perm (Fin n)}
    (hx : IsMinimalRepresentative B (B.flatten S) x)
    (hxc : CuspidalSupport.ConjugatesLevi (F := F) (B.flatten S') (B.flatten S) x)
    (hg : IsMinimalRepresentative (B.flatten Q) (B.flatten S') g)
    (hgW : g ∈ blockWeyl B) :
    IsMinimalRepresentative (B.flatten Q) (B.flatten S) (x * g) := by
  refine ⟨(strictMono_blocks_iff _ (x * g)).mpr fun a b hab hlt => ?_,
    (strictMono_blocks_iff _ (x * g).symm).mpr fun a b hab hlt => ?_⟩
  · have hg' := (strictMono_blocks_iff _ g).mp hg.1 a b hab hlt
    have hB : blockIndex B (g a) = blockIndex B (g b) := by
      rw [hgW a, hgW b, ProductLeviMinimalIndex.blockIndex_eq_flatten B Q a,
        ProductLeviMinimalIndex.blockIndex_eq_flatten B Q b, hab]
    simp only [Equiv.Perm.mul_apply]
    exact (strictMono_blocks_iff B x).mp hx.1 _ _ hB hg'
  · have hx' := (strictMono_blocks_iff _ x.symm).mp hx.2 a b hab hlt
    have hS' : blockIndex (B.flatten S') (x⁻¹ a) = blockIndex (B.flatten S') (x⁻¹ b) :=
      CuspidalSupport.ConjugatesLevi.blockIndex_eq
        (CuspidalSupport.conjugatesLevi_inv hxc) hab
    exact (strictMono_blocks_iff _ g.symm).mp hg.2 _ _ hS' hx'

/-- A product with coarse-Weyl factors lies outside the coarse Weyl group
whenever its first factor does. -/
theorem mul_mul_not_mem_blockWeyl {B : BlockShape n} {x g h : Equiv.Perm (Fin n)}
    (hx : x ∉ blockWeyl B) (hg : g ∈ blockWeyl B) (hh : h ∈ blockWeyl B) :
    x * g * h ∉ blockWeyl B := by
  intro hw
  apply hx
  have := (blockWeyl B).mul_mem ((blockWeyl B).mul_mem hw ((blockWeyl B).inv_mem hh))
    ((blockWeyl B).inv_mem hg)
  simpa [mul_assoc] using this

/-- A middle-Weyl conjugating permutation preserves the middle parents of
fine blocks. -/
theorem parent_blockEquiv {F : Type*} [Field F] (D : BlockShape n) (R R' : BlockRefinement D)
    {h : Equiv.Perm (Fin n)}
    (hh : CuspidalSupport.ConjugatesLevi (F := F) (D.flatten R) (D.flatten R') h)
    (hW : h ∈ blockWeyl D) (k : Fin (D.flatten R).length) :
    ((D.flattenBlockEquiv R').symm (CuspidalSupport.blockEquiv hh k)).1 =
      ((D.flattenBlockEquiv R).symm k).1 := by
  let a := (D.flatten R).index k ⟨0, (D.flatten R).positive k⟩
  change ((D.flattenBlockEquiv R').symm (blockIndex (D.flatten R') (h a))).1 = _
  rw [UnitaryWeylRigidity.flattenBlockEquiv_symm_blockIndex, hW a]
  have hk : blockIndex (D.flatten R) a = k := blockIndex_index _ _ _
  rw [← hk, UnitaryWeylRigidity.flattenBlockEquiv_symm_blockIndex]

end Combinatorics

section Representations

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData) {n : ℕ}

/-- The canonical topology makes the coefficient field a topological ring. -/
theorem topologicalRing_carrier :
    letI := T.topology
    IsTopologicalRing F.Carrier := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  infer_instance

/-- The refined opposite radical lies in the kernel of every coarse complex
determinant character. -/
theorem refinedOppositeUnipotent_le_ker (B : BlockShape n) (S : BlockRefinement B)
    (z : Fin B.length → ℂ) :
    refinedOppositeUnipotent F.Carrier B S ≤ (T.leviComplexPowerCharacter B z).ker := by
  intro u hu
  apply T.normOneLevi_le_ker_leviComplexPowerCharacter B z
  apply (T.mem_normOneLevi B u).mpr
  intro i
  change T.normalizedAbsUnits (determinant (u i)) = 1
  rw [Parabolic.OppositeTransitivity.lower_determinant_one (S i)
    ((mem_refinedOppositeUnipotent F.Carrier B S u).mp hu i), map_one]

/-- The normalized refined opposite Jacquet quotient of a twist maps onto the
restricted twist of the untwisted quotient, class by class. -/
def normalizedTwistJacquetMap (B : BlockShape n) (S : BlockRefinement B)
    (χ : B.Levi F.Carrier →* ℂˣ) (hχ : refinedOppositeUnipotent F.Carrier B S ≤ χ.ker)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (B.Levi F.Carrier) V) :
    (T.normalizedRefinedOppositeJacquet B S (twist χ ρ)).IntertwiningMap
      (twist (χ.comp (refinedLevi F.Carrier B S).subtype)
        (T.normalizedRefinedOppositeJacquet B S ρ)) where
  toLinearMap := (Langlands.Jacquet.twistCoinvariantsLinearEquiv χ ρ _ hχ).toLinearMap
  isIntertwining' m := by
    apply Representation.Coinvariants.hom_ext
    ext v
    change (Langlands.Jacquet.inverseHalfCharacter (T.refinedOppositeLeviModulus B S) m : ℂ) •
        Langlands.Jacquet.mk ρ _ ((χ m.val : ℂ) • ρ m.val v) =
      (χ m.val : ℂ) •
        ((Langlands.Jacquet.inverseHalfCharacter (T.refinedOppositeLeviModulus B S) m : ℂ) •
          Langlands.Jacquet.mk ρ _ (ρ m.val v))
    rw [map_smul]
    exact smul_comm _ _ _

/-- The twisted Jacquet map is surjective. -/
theorem normalizedTwistJacquetMap_surjective (B : BlockShape n) (S : BlockRefinement B)
    (χ : B.Levi F.Carrier →* ℂˣ) (hχ : refinedOppositeUnipotent F.Carrier B S ≤ χ.ker)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (B.Levi F.Carrier) V) :
    Function.Surjective (normalizedTwistJacquetMap T B S χ hχ ρ) :=
  (Langlands.Jacquet.twistCoinvariantsLinearEquiv χ ρ _ hχ).surjective

/-- The actual coinvariant map of a surjective intertwiner is surjective. -/
theorem jacquetMap_surjective {G : Type*} [Group G] {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (N M : Subgroup G) (hMN : M ≤ Subgroup.normalizer N) (f : ρ.IntertwiningMap σ)
    (hf : Function.Surjective f) : Function.Surjective (Langlands.Jacquet.map N M hMN f) := by
  intro y
  obtain ⟨w, rfl⟩ := Langlands.Jacquet.mk_surjective σ N y
  obtain ⟨v, rfl⟩ := hf w
  exact ⟨Langlands.Jacquet.mk ρ N v, rfl⟩

/-- The normalized refined opposite Jacquet map of a surjection is surjective. -/
theorem normalizedRefinedOppositeJacquetMap_surjective (B : BlockShape n)
    (S : BlockRefinement B) {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (B.Levi F.Carrier) V} {σ : Representation ℂ (B.Levi F.Carrier) W}
    (f : ρ.IntertwiningMap σ) (hf : Function.Surjective f) :
    Function.Surjective (T.normalizedRefinedOppositeJacquetMap B S f) :=
  jacquetMap_surjective _ _ le_rfl f hf

/-- Subquotients of a flattened inner Jacquet module pull back along surjections. -/
theorem isSubquotient_innerJacquet_of_surjective (B : BlockShape n) (S : BlockRefinement B)
    {μ : Rep.{uV} ℂ (B.Levi F.Carrier)} {μ' : Rep.{uW} ℂ (B.Levi F.Carrier)}
    (f : μ'.ρ.IntertwiningMap μ.ρ) (hf : Function.Surjective f)
    {X : Type*} [AddCommGroup X] [Module ℂ X]
    {Y : Representation ℂ ((B.flatten S).Levi F.Carrier) X}
    (h : IsSubquotient ((innerJacquet T B S μ).ρ.comp
      (flattenedLeviEquiv F.Carrier B S).toMonoidHom) Y) :
    IsSubquotient ((innerJacquet T B S μ').ρ.comp
      (flattenedLeviEquiv F.Carrier B S).toMonoidHom) Y :=
  ((IsSubquotient.of_surjective (T.normalizedRefinedOppositeJacquetMap B S f)
    (normalizedRefinedOppositeJacquetMap_surjective T B S f hf)).comp _).trans h

/-- A coarse complex determinant twist moves through flattened inner Jacquet
subquotients as the fine twist by the parent exponents. -/
theorem isSubquotient_innerJacquet_twist (B : BlockShape n) (S : BlockRefinement B)
    (z : Fin B.length → ℂ) (μ : Rep.{uV} ℂ (B.Levi F.Carrier))
    {X : Type*} [AddCommGroup X] [Module ℂ X]
    {Y : Representation ℂ ((B.flatten S).Levi F.Carrier) X}
    (h : IsSubquotient ((innerJacquet T B S μ).ρ.comp
      (flattenedLeviEquiv F.Carrier B S).toMonoidHom) Y) :
    IsSubquotient ((innerJacquet T B S (Rep.of (T.leviComplexPowerTwist B z μ.ρ))).ρ.comp
        (flattenedLeviEquiv F.Carrier B S).toMonoidHom)
      (T.leviComplexPowerTwist (B.flatten S)
        (fun k => z ((B.flattenBlockEquiv S).symm k).1) Y) := by
  let χ := T.leviComplexPowerCharacter B z
  let e := flattenedLeviEquiv F.Carrier B S
  have h1 : IsSubquotient
      ((T.normalizedRefinedOppositeJacquet B S (twist χ μ.ρ)).comp e.toMonoidHom)
      (twist ((χ.comp (refinedLevi F.Carrier B S).subtype).comp e.toMonoidHom)
        ((T.normalizedRefinedOppositeJacquet B S μ.ρ).comp e.toMonoidHom)) :=
    (IsSubquotient.of_surjective
      (normalizedTwistJacquetMap T B S χ (refinedOppositeUnipotent_le_ker T B S z) μ.ρ)
      (normalizedTwistJacquetMap_surjective T B S χ
        (refinedOppositeUnipotent_le_ker T B S z) μ.ρ)).comp e.toMonoidHom
  have hχ : (χ.comp (refinedLevi F.Carrier B S).subtype).comp e.toMonoidHom =
      T.leviComplexPowerCharacter (B.flatten S)
        (fun k => z ((B.flattenBlockEquiv S).symm k).1) := by
    have hr := (leviComplexPowerRefinement.{uF, 0} p F T n B S z).2.1
    apply MonoidHom.ext
    intro m
    have := congrArg (fun φ => φ (e m)) hr
    simpa [χ, e] using this
  rw [hχ] at h1
  exact h1.trans (h.twist _)

/-- Transport preserves subquotients. -/
theorem IsSubquotient.transport {E : Type*} [Field E] {B C : BlockShape n}
    {w : Equiv.Perm (Fin n)} (hw : CuspidalSupport.ConjugatesLevi (F := E) B C w)
    {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {A : Representation ℂ (B.Levi E) V} {Y : Representation ℂ (B.Levi E) W}
    (h : IsSubquotient A Y) :
    IsSubquotient (CuspidalSupport.transport B C w hw A)
      (CuspidalSupport.transport B C w hw Y) :=
  h.comp _

/-- Transport depends only on the permutation. -/
theorem transport_congr {E : Type*} [Field E] {B C : BlockShape n}
    {w w' : Equiv.Perm (Fin n)} (h : w = w')
    (hw : CuspidalSupport.ConjugatesLevi (F := E) B C w)
    (hw' : CuspidalSupport.ConjugatesLevi (F := E) B C w')
    {V : Type uV} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (B.Levi E) V) :
    CuspidalSupport.transport B C w hw ρ = CuspidalSupport.transport B C w' hw' ρ := by
  subst h
  rfl

/-- Transport along a permutation equal to the identity is trivial. -/
theorem transport_eq_self {E : Type*} [Field E] {B : BlockShape n}
    {w : Equiv.Perm (Fin n)} (h : w = 1)
    (hw : CuspidalSupport.ConjugatesLevi (F := E) B B w)
    {V : Type uV} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (B.Levi E) V) :
    CuspidalSupport.transport B B w hw ρ = ρ := by
  subst h
  exact CuspidalSupport.transport_one ρ

/-- Transport undoes transport along the inverse permutation. -/
theorem transport_transport_inv {E : Type*} [Field E] {B C : BlockShape n}
    {w : Equiv.Perm (Fin n)} (hw : CuspidalSupport.ConjugatesLevi (F := E) B C w)
    (hw' : CuspidalSupport.ConjugatesLevi (F := E) C B w⁻¹)
    {V : Type uV} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (C.Levi E) V) :
    CuspidalSupport.transport B C w hw (CuspidalSupport.transport C B w⁻¹ hw' ρ) = ρ := by
  rw [← CuspidalSupport.transport_mul hw' hw]
  exact transport_eq_self (mul_inv_cancel w) _ ρ

/-- Undoing two inverse transports and composing three forward ones. -/
theorem transport_chain_equiv {E : Type*} [Field E] {B₁ B₂ B₃ B₄ : BlockShape n}
    {x g d : Equiv.Perm (Fin n)}
    (hx : CuspidalSupport.ConjugatesLevi (F := E) B₂ B₁ x)
    (hg : CuspidalSupport.ConjugatesLevi (F := E) B₃ B₂ g)
    (hd : CuspidalSupport.ConjugatesLevi (F := E) B₄ B₃ d)
    (hw : CuspidalSupport.ConjugatesLevi (F := E) B₄ B₁ (x * g * d))
    {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (B₁.Levi E) V) (ω : Representation ℂ (B₄.Levi E) W)
    (e : (CuspidalSupport.transport B₂ B₃ g⁻¹ (CuspidalSupport.conjugatesLevi_inv hg)
      (CuspidalSupport.transport B₁ B₂ x⁻¹ (CuspidalSupport.conjugatesLevi_inv hx) ρ)).Equiv
        (CuspidalSupport.transport B₄ B₃ d hd ω)) :
    Nonempty (ρ.Equiv (CuspidalSupport.transport B₄ B₁ (x * g * d) hw ω)) := by
  have e4 := CuspidalSupport.transportEquiv x hx (CuspidalSupport.transportEquiv g hg e)
  rw [transport_transport_inv, transport_transport_inv,
    ← CuspidalSupport.transport_mul hd hg, ← CuspidalSupport.transport_mul _ hx,
    transport_congr (mul_assoc x g d).symm _ hw] at e4
  exact ⟨e4⟩

/-- Irreducibility survives the cast along an equality of shapes. -/
theorem cast_isIrreducible {E E' : BlockShape n} (h : E = E')
    (ω : Rep.{uV} ℂ (E.Levi F.Carrier)) (hω : Representation.IsIrreducible ω.ρ) :
    Representation.IsIrreducible (h ▸ ω : Rep.{uV} ℂ (E'.Levi F.Carrier)).ρ := by
  subst h
  exact hω

/-- Cuspidality survives the cast along an equality of shapes. -/
theorem cast_isLeviCuspidal {E E' : BlockShape n} (h : E = E')
    (ω : Rep.{uV} ℂ (E.Levi F.Carrier)) :
    letI := T.topology
    CuspidalSupport.IsLeviCuspidal E ω.ρ →
      CuspidalSupport.IsLeviCuspidal E' (h ▸ ω : Rep.{uV} ℂ (E'.Levi F.Carrier)).ρ := by
  subst h
  exact id

/-- Unitarizability survives the cast along an equality of shapes. -/
theorem cast_isUnitarizable {E E' : BlockShape n} (h : E = E')
    (ω : Rep.{uV} ℂ (E.Levi F.Carrier)) (hω : IsUnitarizable ω.ρ) :
    IsUnitarizable (h ▸ ω : Rep.{uV} ℂ (E'.Levi F.Carrier)).ρ := by
  subst h
  exact hω

/-- A cast parameter evaluates at block indices as the original one. -/
theorem cast_param_blockIndex {E E' : BlockShape n} (h : E = E')
    (v : Fin E.length → ℝ) (a : Fin n) :
    (h ▸ v : Fin E'.length → ℝ) (blockIndex E' a) = v (blockIndex E a) := by
  subst h
  rfl

/-- A zero fine twist is the untwisted flattened action. -/
theorem fineTwist_zero_zero (B : BlockShape n) (Q : BlockRefinement B)
    (σ : Rep.{uV} ℂ ((B.flatten Q).Levi F.Carrier)) :
    fineTwist T B Q σ 0 0 =
      Rep.of (σ.ρ.comp (flattenedLeviEquiv F.Carrier B Q).symm.toMonoidHom) := by
  have h : (fun k => -(0 : Fin (B.flatten Q).length → ℝ) k +
      (0 : Fin B.length → ℝ) ((B.flattenBlockEquiv Q).symm k).1) = 0 := by
    funext k
    simp
  unfold fineTwist
  rw [h, T.leviRealPowerTwist_zero]

/-- With zero fine offset the fine twist is the parent coarse twist. -/
theorem fineTwist_zero_left (B : BlockShape n) (Q : BlockRefinement B)
    (σ : Rep.{uV} ℂ ((B.flatten Q).Levi F.Carrier)) (t : Fin B.length → ℝ) :
    fineTwist T B Q σ 0 t =
      Rep.of ((T.leviRealPowerTwist (B.flatten Q)
        (fun k => t ((B.flattenBlockEquiv Q).symm k).1) σ.ρ).comp
          (flattenedLeviEquiv F.Carrier B Q).symm.toMonoidHom) := by
  have h : (fun k => -(0 : Fin (B.flatten Q).length → ℝ) k +
      t ((B.flattenBlockEquiv Q).symm k).1) =
        fun k => t ((B.flattenBlockEquiv Q).symm k).1 := by
    funext k
    simp
  unfold fineTwist
  rw [h]

end Representations


end WeylBranchPieces

open WeylBranchPieces

universe uF uV uM uW

/-- The supported excess-multiplicity Weyl-branch obstruction follows from the
four Weyl-piece interfaces. The branch is `w = x g d`, with `x` from the excess
interface, `g` from the product-Levi localization and `d` from the cuspidal
constituent interface; the occurrence holds at every middle unitary parameter. -/
theorem glSupportedRegularMultiplicityBranchObstruction_of_pieces
    (hP3 : GLGeometricPieceLiftingStatement.{uF, uM})
    (hP1 : GLGeometricExcessBranchStatement.{uF, uV, uW})
    (hP2 : GLProductLeviCuspidalLocalizationStatement.{uF, uV, uM})
    (hP2c : GLCuspidalInductionJacquetConstituentStatement.{uF, uV, uV}) :
    GLSupportedRegularMultiplicityBranchObstructionStatement.{uF, uV, uM, uW} := by
  intro p _ F T
  let := T.topology
  intro n hn B Q D R S hSR ω hωirr hωcusp hωunit v₀ _hv₀ ωB vB σ _hσirr _hσsq hσq
    π _hπirr _hπtemp hπmid _hπS t _ht τ πt m_in m_amb hin hamb hlt C
  have hTR : IsTopologicalRing F.Carrier := topologicalRing_carrier T
  obtain ⟨qσ, hqσ⟩ := hσq
  obtain ⟨qπ, hqπ⟩ := hπmid
  -- smoothness
  have hσsm : IsSmooth σ.ρ :=
    isSmooth_of_surjective qσ hqσ (T.isSmooth_normalizedRefinedInduced D R _)
  have hπsm : IsSmooth π.ρ :=
    isSmooth_of_surjective qπ hqπ (T.isSmooth_normalizedRefinedInduced B Q _)
  have hπtsm : IsSmooth πt.ρ := (T.isSmooth_leviRealPowerTwist_iff B t π.ρ).mpr hπsm
  -- the middle real twist
  let t' : Fin D.length → ℝ := fun k => t ((B.flattenBlockEquiv Q).symm k).1
  let σt : Rep.{uM} ℂ (D.Levi F.Carrier) := Rep.of (T.leviRealPowerTwist D t' σ.ρ)
  have hσtsm : IsSmooth σt.ρ := (T.isSmooth_leviRealPowerTwist_iff D t' σ.ρ).mpr hσsm
  obtain ⟨qmid, hqmid⟩ :
      ∃ q : (middleInduced T B Q σt).ρ.IntertwiningMap πt.ρ, Function.Surjective q := by
    have h0 : ∃ q : (innerInduced T B Q (fineTwist T B Q σ 0 0)).ρ.IntertwiningMap π.ρ,
        Function.Surjective q := by
      rw [fineTwist_zero_zero]
      exact ⟨qπ, hqπ⟩
    obtain ⟨q₀, hq₀⟩ := h0
    have hRLT := refinedLeviRealTwist.{uF, uM, uW} p F T n B Q σ 0 t
    obtain ⟨-, _E, -, -, hlift⟩ := hRLT
    obtain ⟨q, hq, -⟩ := hlift π q₀ hq₀
    have h1 : ∃ q : (innerInduced T B Q (fineTwist T B Q σ 0 t)).ρ.IntertwiningMap πt.ρ,
        Function.Surjective q := ⟨q, hq⟩
    rw [fineTwist_zero_left] at h1
    exact h1
  -- the fine coarse-twisted cuspidal representation
  let sB : Fin (B.flatten S).length → ℝ :=
    fun k => -vB k + t ((B.flattenBlockEquiv S).symm k).1
  let ρB : Rep.{uV} ℂ ((B.flatten S).Levi F.Carrier) :=
    Rep.of (T.leviRealPowerTwist (B.flatten S) sB ωB.ρ)
  have hωBirr : Representation.IsIrreducible ωB.ρ := cast_isIrreducible hSR ω hωirr
  have hωBcusp : CuspidalSupport.IsLeviCuspidal (B.flatten S) ωB.ρ :=
    cast_isLeviCuspidal T hSR ω hωcusp
  have hωBunit : IsUnitarizable ωB.ρ := cast_isUnitarizable hSR ω hωunit
  have hvB : ∀ a : Fin n, vB (blockIndex (B.flatten S) a) = v₀ (blockIndex C a) :=
    cast_param_blockIndex hSR v₀
  clear_value ωB vB
  have hρBirr : Representation.IsIrreducible ρB.ρ :=
    (T.isIrreducible_leviRealPowerTwist_iff (B.flatten S) sB ωB.ρ).mpr hωBirr
  have hρBcusp : CuspidalSupport.IsLeviCuspidal (B.flatten S) ρB.ρ :=
    (T.isLeviCuspidal_leviRealPowerTwist_iff (B.flatten S) sB ωB.ρ).mpr hωBcusp
  -- (P1) the excess branch
  obtain ⟨x, S', hx, hxmin, hxW, hxsub⟩ :=
    hP1 p F T n hn B S πt hπtsm ρB hρBirr hρBcusp m_in m_amb hin hamb hlt
  have hxinv := CuspidalSupport.conjugatesLevi_inv hx
  let ρ2 : Rep.{uV} ℂ ((B.flatten S').Levi F.Carrier) :=
    Rep.of (CuspidalSupport.transport (B.flatten S) (B.flatten S') x⁻¹ hxinv ρB.ρ)
  have hsub2 : IsSubquotient ((innerJacquet T B S' πt).ρ.comp
      (flattenedLeviEquiv F.Carrier B S').toMonoidHom) ρ2.ρ := by
    have h := IsSubquotient.of_comp_symm
      (CuspidalSupport.leviConjugation (F := F.Carrier) _ _ x hx) hxsub
    show IsSubquotient _ (CuspidalSupport.transport (B.flatten S) (B.flatten S') x⁻¹ hxinv ρB.ρ)
    rw [CuspidalSupport.transport_inv hx]
    exact h
  have hxmin' : IsMinimalRepresentative (B.flatten S) (B.flatten S') x⁻¹ :=
    IsMinimalRepresentative.inv (IsMinimalRepresentative.flatten_left S' hxmin)
  have hρ2irr : Representation.IsIrreducible ρ2.ρ :=
    (CuspidalSupport.isIrreducible_transport x⁻¹ hxinv ρB.ρ).mpr hρBirr
  have hρ2cusp : CuspidalSupport.IsLeviCuspidal (B.flatten S') ρ2.ρ :=
    ⟨CuspidalSupport.isAdmissible_transport x⁻¹ hxinv hρBcusp.1,
      CuspidalSupport.isLeviQuasicuspidal_transport _ _ x⁻¹ hxmin' hxinv ρB.ρ hρBcusp.2⟩
  -- (P2) localization in the coarse Levi
  have hsub2' : IsSubquotient ((innerJacquet T B S' (middleInduced T B Q σt)).ρ.comp
      (flattenedLeviEquiv F.Carrier B S').toMonoidHom) ρ2.ρ :=
    isSubquotient_innerJacquet_of_surjective T B S' qmid hqmid hsub2
  obtain ⟨g, hgW, R', hg, hgmin, hgsub⟩ :=
    hP2 p F T n hn B Q σt hσtsm S' ρ2 hρ2irr hρ2cusp hsub2'
  have hginv := CuspidalSupport.conjugatesLevi_inv hg
  let ρ3 : Rep.{uV} ℂ ((D.flatten R').Levi F.Carrier) :=
    Rep.of (CuspidalSupport.transport (B.flatten S') (D.flatten R') g⁻¹ hginv ρ2.ρ)
  have hsub3 : IsSubquotient ((innerJacquet T D R' σt).ρ.comp
      (flattenedLeviEquiv F.Carrier D R').toMonoidHom) ρ3.ρ := by
    have h := IsSubquotient.of_comp_symm
      (CuspidalSupport.leviConjugation (F := F.Carrier) _ _ g hg) hgsub
    show IsSubquotient _ (CuspidalSupport.transport (B.flatten S') (D.flatten R') g⁻¹ hginv ρ2.ρ)
    rw [CuspidalSupport.transport_inv hg]
    exact h
  have hgmin' : IsMinimalRepresentative (B.flatten S') (D.flatten R') g⁻¹ :=
    IsMinimalRepresentative.inv (IsMinimalRepresentative.flatten_left R' hgmin)
  have hρ3irr : Representation.IsIrreducible ρ3.ρ :=
    (CuspidalSupport.isIrreducible_transport g⁻¹ hginv ρ2.ρ).mpr hρ2irr
  have hρ3cusp : CuspidalSupport.IsLeviCuspidal (D.flatten R') ρ3.ρ :=
    ⟨CuspidalSupport.isAdmissible_transport g⁻¹ hginv hρ2cusp.1,
      CuspidalSupport.isLeviQuasicuspidal_transport _ _ g⁻¹ hgmin' hginv ρ2.ρ hρ2cusp.2⟩
  -- the middle-level real twist of the cuspidal datum
  let sC : Fin C.length → ℝ := fun k => -v₀ k + t' ((D.flattenBlockEquiv R).symm k).1
  let ω' : Rep.{uV} ℂ (C.Levi F.Carrier) := Rep.of (T.leviRealPowerTwist C sC ω.ρ)
  have hω'irr : Representation.IsIrreducible ω'.ρ :=
    (T.isIrreducible_leviRealPowerTwist_iff C sC ω.ρ).mpr hωirr
  have hω'cusp : CuspidalSupport.IsLeviCuspidal C ω'.ρ :=
    (T.isLeviCuspidal_leviRealPowerTwist_iff C sC ω.ρ).mpr hωcusp
  obtain ⟨qD, hqD⟩ : ∃ q : (innerInduced T D R (Rep.of (ω'.ρ.comp
      (flattenedLeviEquiv F.Carrier D R).symm.toMonoidHom))).ρ.IntertwiningMap σt.ρ,
      Function.Surjective q := by
    have hRLT := refinedLeviRealTwist.{uF, uV, uM} p F T n D R ω v₀ t'
    obtain ⟨-, _E, -, -, hlift⟩ := hRLT
    obtain ⟨q, hq, -⟩ := hlift σ qσ hqσ
    exact ⟨q, hq⟩
  have hsub3' := isSubquotient_innerJacquet_of_surjective T D R' qD hqD hsub3
  -- (P2c) the cuspidal constituent
  obtain ⟨d, hdW, hd, ⟨e3⟩⟩ :=
    hP2c p F T n hn D R R' ω' hω'irr hω'cusp ρ3 hρ3irr hρ3cusp hsub3'
  -- the branch and its conjugacy witnesses
  have hxg' : CuspidalSupport.ConjugatesLevi (F := F.Carrier) (D.flatten R') (B.flatten S)
      (x * g) := CuspidalSupport.conjugatesLevi_mul hg hx
  have hw' : CuspidalSupport.ConjugatesLevi (F := F.Carrier) C (B.flatten S) (x * g * d) :=
    CuspidalSupport.conjugatesLevi_mul hd hxg'
  have hxg : CuspidalSupport.ConjugatesLevi (F := F.Carrier) (D.flatten R') C (x * g) := by
    have h := hxg'
    rw [← hSR] at h
    exact h
  have hw : CuspidalSupport.ConjugatesLevi (F := F.Carrier) C C (x * g * d) := by
    have h := hw'
    rw [← hSR] at h
    exact h
  have hxgmin : IsMinimalRepresentative D C (x * g) := by
    have h := isMinimalRepresentative_mul (F := F.Carrier) Q S S' hxmin hx hgmin hgW
    rw [← hSR] at h
    exact h
  -- the equivalence ρB ≃ transport (x g d) ω'
  have heq : Nonempty (ρB.ρ.Equiv
      (CuspidalSupport.transport C (B.flatten S) (x * g * d) hw' ω'.ρ)) := by
    exact transport_chain_equiv hx hg hd hw' ρB.ρ ω'.ρ e3
  refine ⟨x * g * d, hw, ?_, ?_, ?_⟩
  · exact mul_mul_not_mem_blockWeyl hxW hgW
      (ProductLeviMinimalIndex.blockWeyl_flatten_le B Q hdW)
  · obtain ⟨e⟩ := heq
    have hrig := (glUnitaryWeylRealExponentRigidity.{uF, uV, uV} p F T n hn C).2.1
      (B.flatten S) _ _ ω.ρ ωB.ρ hωirr hωcusp.1 hωunit hωBirr hωBcusp.1 hωBunit
      sC sB (x * g * d) hw' ⟨e.symm⟩
    intro a
    have key : ∀ b : Fin n,
        -v₀ (blockIndex C ((x * g * d) b)) + t (blockIndex B ((x * g * d) b)) =
          -v₀ (blockIndex C b) + t (blockIndex B b) := by
      intro b
      have h := hrig b
      simp only [sB, sC, t', C, D,
        UnitaryWeylRigidity.flattenBlockEquiv_symm_blockIndex] at h
      rw [hvB] at h
      exact h
    have h := key ((x * g * d).symm a)
    rw [Equiv.apply_symm_apply] at h
    linear_combination h
  · refine Filter.Eventually.of_forall fun u => ?_
    -- the constituent at the real parameter
    have hA : IsSubquotient ((innerJacquet T D R' σt).ρ.comp
        (flattenedLeviEquiv F.Carrier D R').toMonoidHom)
        (CuspidalSupport.transport C (D.flatten R') d hd ω'.ρ) :=
      hsub3.of_equiv_right e3
    -- move to the unitary middle parameter
    let z : Fin D.length → ℂ := fun i => Complex.I * (u i : ℂ) - (t' i : ℂ)
    have hB := isSubquotient_innerJacquet_twist T D R' z σt hA
    have hσu : Rep.of (T.leviComplexPowerTwist D z σt.ρ) =
        Rep.of (T.leviComplexPowerTwist D (ComplexTwistFamilies.unitaryAmbient D u) σ.ρ) := by
      congr 1
      show T.leviComplexPowerTwist D z (T.leviRealPowerTwist D t' σ.ρ) = _
      rw [← T.leviComplexPowerTwist_ofReal, ← T.leviComplexPowerTwist_add]
      congr 1
      funext i
      simp [z]
    have hcand : T.leviComplexPowerTwist (D.flatten R')
        (fun k => z ((D.flattenBlockEquiv R').symm k).1)
        (CuspidalSupport.transport C (D.flatten R') d hd ω'.ρ) =
        CuspidalSupport.transport C (D.flatten R') d hd
          (T.leviComplexPowerTwist C
            (ComplexTwistFamilies.refinedMixedAffine D R (-v₀) u) ω.ρ) := by
      have hω' : ω'.ρ = T.leviComplexPowerTwist C (fun k => (sC k : ℂ)) ω.ρ :=
        (T.leviComplexPowerTwist_ofReal C sC ω.ρ).symm
      rw [hω', T.transport_leviComplexPowerTwist, T.transport_leviComplexPowerTwist,
        ← T.leviComplexPowerTwist_add]
      congr 1
      funext j
      have hp := parent_blockEquiv D R R' hd hdW ((CuspidalSupport.blockEquiv hd).symm j)
      rw [Equiv.apply_symm_apply] at hp
      simp only [Pi.add_apply, z, sC, ComplexTwistFamilies.refinedMixedAffine_apply, hp,
        Pi.neg_apply]
      push_cast
      ring
    rw [hσu, hcand] at hB
    -- lift through the whole-Levi geometric piece
    have hσusm : IsSmooth
        (T.leviComplexPowerTwist D (ComplexTwistFamilies.unitaryAmbient D u) σ.ρ) :=
      (T.isSmooth_leviComplexPowerTwist_iff D _ σ.ρ).mpr hσsm
    have hP := hP3 p F T n hn D C R' (x * g) hxgmin hxg
      (Rep.of (T.leviComplexPowerTwist D (ComplexTwistFamilies.unitaryAmbient D u) σ.ρ)) hσusm
    have hfin := hP.trans (hB.transport hxg)
    rw [← CuspidalSupport.transport_mul hd hxg] at hfin
    have hirr : Representation.IsIrreducible (CuspidalSupport.transport C C (x * g * d) hw
        (T.leviComplexPowerTwist C
          (ComplexTwistFamilies.refinedMixedAffine D R (-v₀) u) ω.ρ)) :=
      (CuspidalSupport.isIrreducible_transport _ hw _).mpr
        ((isIrreducible_twist_iff _ ω.ρ).mpr hωirr)
    have hadm : IsAdmissible (CuspidalSupport.transport C C (x * g * d) hw
        (T.leviComplexPowerTwist C
          (ComplexTwistFamilies.refinedMixedAffine D R (-v₀) u) ω.ρ)) :=
      CuspidalSupport.isAdmissible_transport _ hw
        ((isAdmissible_twist_iff _ ω.ρ (T.isOpen_ker_leviComplexPowerCharacter C _)).mpr
          hωcusp.1)
    exact (ComplexTwistFamilies.occurs_iff T D C C σ (x * g * d) hw ω _ _ u).mpr
      ⟨hirr, hadm, hfin⟩


end Langlands
