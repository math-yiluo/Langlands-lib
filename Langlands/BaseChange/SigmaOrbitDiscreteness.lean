import Langlands.AllField.Representation.Induction.Equivalences
import Langlands.BaseChange.SigmaOrbitStability
import Langlands.BaseChange.UnitarySigmaOrbitProduct
import Langlands.Representation.Induction.BlockInducingRecovery
import Langlands.Representation.Classification.IrreducibleProductFiniteLengthProof
import Langlands.Representation.Classification.SupercuspidalSupportUniquenessProof
import Langlands.Representation.CuspidalSupport.LeviAdmissibleFactorizationProof
import Langlands.Representation.Tensor.ExternalSubquotient

/-! # The supercuspidal orbit product is σ-discrete after unitarization -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.BaseChange

open GeneralLinear Classification Geometric

universe u v uW

variable {F : Type u} [Field F] [TopologicalSpace F]
  {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [CharZero E] [Algebra F E] [IsModuleTopology F E]

local notation "K" => CharZeroLocalField.padicField E
local notation "T" => CharZeroLocalField.topologicalData E
local notation "D" => LocalFieldData.ofInstances E

private def conjugateCuspidal (σ : E ≃ₐ[F] E) {m : ℕ}
    (C : SupercuspidalRep.{v, uW} (F := E) (n := m)) :
    SupercuspidalRep.{v, uW} (F := E) (n := m) :=
  let ρ := C.obj.representation
  let hsc := isSupercuspidal_comp_entrywiseAut σ ρ C.property.2
  ⟨SmoothRep.of (ρ.comp (entrywiseAut σ m).toMonoidHom) hsc.1.1,
    (CuspidalSupport.isIrreducible_comp_mulEquiv_iff ρ (entrywiseAut σ m)).mpr C.property.1, hsc⟩

private def datum {m : ℕ} (hm : 0 < m) (C : SupercuspidalRep.{v, uW} (F := E) (n := m)) :
    (T).CuspidalDatum.{uW,v} :=
  ⟨m, hm, C.isoClass⟩

private theorem datum_eq_iff {m : ℕ} (hm : 0 < m)
    (C C' : SupercuspidalRep.{v, uW} (F := E) (n := m)) :
    datum hm C = datum hm C' ↔ Nonempty (C.obj.representation.Equiv C'.obj.representation) := by
  constructor
  · intro h
    have hc : C.isoClass = C'.isoClass := by injection h
    obtain ⟨e⟩ := (SupercuspidalRep.isoClass_eq_iff C C').mp hc
    exact ⟨SmoothRep.equivOfIso ((ObjectProperty.ι _).mapIso e)⟩
  · rintro ⟨e⟩
    exact congrArg (fun c => (⟨m, hm, c⟩ : (T).CuspidalDatum.{uW,v}))
      ((SupercuspidalRep.isoClass_eq_iff C C').mpr ⟨ObjectProperty.isoMk _ (SmoothRep.mkIso e)⟩)

private def conjugateDatum (σ : E ≃ₐ[F] E) (ρ : (T).CuspidalDatum.{uW,v}) :
    (T).CuspidalDatum.{uW,v} where
  rank := ρ.rank
  rank_pos := ρ.rank_pos
  cls := Quotient.map (conjugateCuspidal σ) (by
    intro C C' h
    obtain ⟨e⟩ := h
    exact ⟨ObjectProperty.isoMk _ (SmoothRep.mkIso (BinaryTensor.compEquiv
      (SmoothRep.equivOfIso ((ObjectProperty.ι _).mapIso e))
      (entrywiseAut σ ρ.rank).toMonoidHom))⟩) ρ.cls

private theorem conjugateDatum_datum (σ : E ≃ₐ[F] E) {m : ℕ} (hm : 0 < m)
    (C : SupercuspidalRep.{v, uW} (F := E) (n := m)) :
    conjugateDatum σ (datum hm C) = datum hm (conjugateCuspidal σ C) := rfl

private theorem support_of_embedding {m : ℕ} (B : BlockShape m)
    (C : ∀ j, SupercuspidalRep.{v, uW} (F := E) (n := B.size j))
    (A : SmoothRep.{0, v, max v uW} ℂ (GeneralLinear m E)) (hA : A.IsIrreducible)
    (J : A.representation.IntertwiningMap
      ((T).normalizedProductInduced B (fun j => (C j).obj.representation)))
    (hJ : Function.Injective J.toLinearMap) :
    (T).IsSupercuspidalSupport A
      (List.ofFn (fun j => datum (B.positive j) (C j))) := by
  let : TopologicalSpace (K).Carrier := ‹TopologicalSpace E›
  cases B with
  | mk length size positive sum_eq =>
    refine ⟨length, (fun j => datum (positive j) (C j)), rfl, sum_eq, C, fun _ => rfl, hA, ?_⟩
    exact SmoothRep.IsSubrepresentation.isSubquotient ⟨SmoothRep.ofHom J, hJ⟩

set_option maxHeartbeats 1000000 in
private theorem support_of_conjugate {m : ℕ} (σ : E ≃ₐ[F] E) (hm : 0 < m)
    (B : BlockShape m) (C : ∀ j, SupercuspidalRep.{v, uW} (F := E) (n := B.size j))
    (A : SmoothRep.{0, v, max v uW} ℂ (GeneralLinear m E)) (hA : A.IsIrreducible)
    (e : A.representation.Equiv (A.representation.comp (entrywiseAut σ m).toMonoidHom))
    (J : A.representation.IntertwiningMap
      ((T).normalizedProductInduced B (fun j => (C j).obj.representation)))
    (hJ : Function.Injective J.toLinearMap) (j : Fin B.length) :
    ∃ j', datum (B.positive j') (C j') = conjugateDatum σ (datum (B.positive j) (C j)) := by
  let : TopologicalSpace (K).Carrier := ‹TopologicalSpace E›
  let C' := fun i => conjugateCuspidal σ (C i)
  let e' := normalizedProductInducedEntrywiseAutEquiv σ B (fun i => (C i).obj.representation)
  let J' := e'.toIntertwiningMap.comp
    ((BinaryTensor.compMap J (entrywiseAut σ m).toMonoidHom).comp e.toIntertwiningMap)
  have hJ' : Function.Injective J'.toLinearMap := e'.injective.comp (hJ.comp e.injective)
  have h := glSupercuspidalSupportUniqueness.{uW,v} _ (K) (T) m hm A hA _ _
    (support_of_embedding B C A hA J hJ) (support_of_embedding B C' A hA J' hJ')
  have hj : datum (B.positive j) (C' j) ∈ (List.ofFn (fun i => datum (B.positive i) (C' i)) :
      Multiset ((T).CuspidalDatum.{uW,v})) := Multiset.mem_coe.mpr (List.mem_ofFn.mpr ⟨j, rfl⟩)
  rw [← h, Multiset.mem_coe, List.mem_ofFn] at hj
  simpa only [C', conjugateDatum_datum] using hj

private theorem block_of_rotate_constant {s : ℕ} (hs : 0 < s) {ι : Type*}
    (block : Fin s → ι) (h : ∀ i, block (finRotate s i) = block i) (i j : Fin s) :
    block i = block j := by
  let : NeZero s := ⟨hs.ne'⟩
  have hf (k : ℕ) (a : Fin s) : block ((finRotate s)^[k] a) = block a := by
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', h, ih]
  have he : finCycle (j - i) i = j := by simp [sub_eq_add_neg]
  rw [finCycle_eq_finRotate_iterate] at he
  exact (hf (j - i).val i).symm.trans (congrArg block he)

set_option maxHeartbeats 1000000 in
private theorem proper_levi_not_of_sigma_stability {m : ℕ} (σ : E ≃ₐ[F] E)
    {s : ℕ} (hs : 0 < s) (hn : 0 < m)
    (R : Fin s → SupercuspidalRep.{v, max v uW} (F := E) (n := m))
    (hR : Function.Injective (fun k => datum hn (R k)))
    (hrotate : ∀ k, conjugateDatum σ (datum hn (R k)) = datum hn (R (finRotate s k)))
    (B : BlockShape (s * m)) (hB : 2 ≤ B.length)
    (A : ∀ i, SmoothRep.{0, v, max v uW} ℂ (GeneralLinear (B.size i) E))
    (hAi : ∀ i, (A i).IsIrreducible)
    (hAσ : ∀ i, Nonempty ((A i).representation.Equiv
      ((A i).representation.comp (entrywiseAut σ (B.size i)).toMonoidHom)))
    (e : ((T).normalizedProductInduced B (fun i => (A i).representation)).Equiv
      ((T).normalizedProductInduced (BlockShape.uniform s m hn) (fun k => (R k).obj.representation)))
    (hI : ((T).normalizedProductInduced B (fun i => (A i).representation)).IsIrreducible) : False := by
  classical
  let : TopologicalSpace (K).Carrier := ‹TopologicalSpace E›
  let : ValuativeRel (K).Carrier := ‹ValuativeRel E›
  let : IsNonarchimedeanLocalField (K).Carrier := ‹IsNonarchimedeanLocalField E›
  have hpos := Nat.mul_pos hs hn
  have hEmb (i : Fin B.length) : ∃ (S : BlockShape (B.size i))
      (C : ∀ j, SupercuspidalRep.{v, max v uW} (F := E) (n := S.size j)),
      ∃ j : (A i).representation.IntertwiningMap
        ((T).normalizedProductInduced S (fun k => (C k).obj.representation)),
        Function.Injective j.toLinearMap :=
    irreducible_supercuspidalProduct_embedding.{v,max v uW,max v uW}
      (K) (T) (B.size i) (B.positive i) (A i) (hAi i)
  choose S C j hj using hEmb
  let q := B.flattenBlockEquiv S
  let Cflat (k : Fin (B.flatten S).length) := C (q.symm k).1 (q.symm k).2
  have hcast (a : (i : Fin B.length) × Fin (S i).length) :
      (B.flatten_size_flattenBlockEquiv S a) ▸ (Cflat (q a)).obj = (C a.1 a.2).obj := by
    have key (x y : (i : Fin B.length) × Fin (S i).length) (h : x = y) :
        (congrArg (fun z => (S z.1).size z.2) h) ▸ (C x.1 x.2).obj = (C y.1 y.2).obj := by
      cases h
      rfl
    exact key _ _ (q.symm_apply_apply a)
  let hrank (a : (i : Fin B.length) × Fin (S i).length) :=
    (B.flatten_size_flattenBlockEquiv S a).symm
  obtain ⟨ereg⟩ := Parabolic.orderedProductRegrouping.{v,max v uW} (K) (T)
    (s * m) (B.flatten S) B S q hrank
    (fun i j x => B.index_index_eq_flatten S ⟨i,j⟩ x) (fun k => (Cflat k).obj)
  have ereg' : ((T).normalizedProductInductionFunctor (B.flatten S)).obj (fun k => (Cflat k).obj) ≅
      ((T).normalizedProductInductionFunctor B).obj (fun i =>
        ((T).normalizedProductInductionFunctor (S i)).obj (fun k => (C i k).obj)) := by
    refine ereg ≪≫ ((T).normalizedProductInductionFunctor B).mapIso (Pi.isoMk fun i => ?_)
    refine ((T).normalizedProductInductionFunctor (S i)).mapIso (Pi.isoMk fun j => ?_)
    exact eqToIso (hcast ⟨i, j⟩)
  let Aprod : SmoothRep.{0,v,max v uW} ℂ (GeneralLinear (s * m) E) :=
    ((T).normalizedProductInductionFunctor B).obj A
  obtain ⟨J, hJ⟩ := normalizedProduct_embedding_of_factor_embeddings (K) (T) B A
    (fun i => ((T).normalizedProductInductionFunctor (S i)).obj (fun j => (C i j).obj)) j hj
  let ereg'' := SmoothRep.equivOfIso ereg'
  let Jflat := ereg''.symm.toIntertwiningMap.comp J
  have hJflat : Function.Injective Jflat.toLinearMap := ereg''.symm.injective.comp hJ
  let Rdata (k : Fin s) := datum (E := E) hn (R k)
  let Cdata (k : Fin (B.flatten S).length) := datum (E := E) ((B.flatten S).positive k) (Cflat k)
  have hflat (a : (i : Fin B.length) × Fin (S i).length) :
      Cdata (q a) = datum (E := E) ((S a.1).positive a.2) (C a.1 a.2) := by
    have key (x y : (i : Fin B.length) × Fin (S i).length) (h : x = y) :
        datum (E := E) ((S x.1).positive x.2) (C x.1 x.2) = datum (E := E) ((S y.1).positive y.2) (C y.1 y.2) := by
      cases h
      rfl
    exact key _ _ (q.symm_apply_apply a)
  have hsame : (List.ofFn Cdata : Multiset ((T).CuspidalDatum.{max v uW,v})) = List.ofFn Rdata :=
    glSupercuspidalSupportUniqueness.{max v uW,v} _ (K) (T) _ hpos Aprod hI _ _
      (support_of_embedding (E := E) (B.flatten S) Cflat Aprod hI Jflat hJflat)
      (support_of_embedding (BlockShape.uniform s m hn) R Aprod hI e.toIntertwiningMap e.injective)
  have hCinj : Function.Injective Cdata := List.nodup_ofFn.mp (Multiset.coe_nodup.mp
    (hsame.symm ▸ Multiset.coe_nodup.mpr (List.nodup_ofFn.mpr hR)))
  have hindex (k : Fin s) : ∃ a, Cdata a = Rdata k := by
    have hk : Rdata k ∈ (List.ofFn Rdata : Multiset _) := Multiset.mem_coe.mpr
      (List.mem_ofFn.mpr ⟨k, rfl⟩)
    rw [← hsame, Multiset.mem_coe, List.mem_ofFn] at hk
    exact hk
  let index (k : Fin s) := q.symm (hindex k).choose
  have hindex_eq (k : Fin s) : Cdata (q (index k)) = Rdata k := by
    simpa only [index, q.apply_symm_apply] using (hindex k).choose_spec
  have hstep (k : Fin s) : (index (finRotate s k)).1 = (index k).1 := by
    let a := index k
    obtain ⟨j', hj'⟩ := support_of_conjugate (E := E) σ (B.positive a.1) (S a.1) (C a.1) (A a.1)
      (hAi a.1) (hAσ a.1).some (j a.1) (hj a.1) a.2
    have ht : Cdata (q ⟨a.1,j'⟩) = Cdata (q (index (finRotate s k))) := by
      rw [hflat, hj', ← hflat a, hindex_eq k, hrotate, hindex_eq]
    have he : (⟨a.1, j'⟩ : (i : Fin B.length) × Fin (S i).length) = index (finRotate s k) :=
      q.injective (hCinj ht)
    have hfirst := congrArg (fun x : (i : Fin B.length) × Fin (S i).length => x.1) he.symm
    exact hfirst
  have honto (i : Fin B.length) : ∃ k, (index k).1 = i := by
    have hi : 0 < (S i).length := by
      by_contra! hz
      have hz' : (S i).length = 0 := by omega
      have hsum := (S i).sum_eq
      simp [hz'] at hsum
      exact (B.positive i).ne' hsum.symm
    let a : (i : Fin B.length) × Fin (S i).length := ⟨i, ⟨0, hi⟩⟩
    have ha : Cdata (q a) ∈ (List.ofFn Cdata : Multiset _) := Multiset.mem_coe.mpr
      (List.mem_ofFn.mpr ⟨q a, rfl⟩)
    rw [hsame, Multiset.mem_coe, List.mem_ofFn] at ha
    obtain ⟨k, hk⟩ := ha
    exact ⟨k, congrArg Sigma.fst (q.injective (hCinj ((hindex_eq k).trans hk)))⟩
  obtain ⟨i, hi⟩ := honto ⟨0, by omega⟩
  obtain ⟨j, hj'⟩ := honto ⟨1, by omega⟩
  have hab := block_of_rotate_constant hs (fun k => (index k).1) hstep i j
  rw [hi, hj'] at hab
  exact Nat.zero_ne_one (congrArg Fin.val hab)

omit [TopologicalSpace F] [ValuativeRel E] [IsNonarchimedeanLocalField E] [CharZero E]
  [IsModuleTopology F E] in
private theorem blockFactors_sigma_stable (σ : E ≃ₐ[F] E) {n : ℕ} (B : BlockShape n)
    (A : ∀ i, SmoothRep.{0, v, max v uW} ℂ (GeneralLinear (B.size i) E))
    (hA : ∀ i, (A i).IsIrreducible)
    (h : IsLeviSigmaStable σ B (B.blockTensor (fun i => (A i).representation))) :
    ∀ i, Nonempty ((A i).representation.Equiv
      ((A i).representation.comp (entrywiseAut σ (B.size i)).toMonoidHom)) := by
  classical
  obtain ⟨e⟩ := h
  let ρ (i : Fin B.length) := (A i).representation
  let ρ' (i : Fin B.length) := (ρ i).comp (entrywiseAut σ (B.size i)).toMonoidHom
  have e' : (FiniteTensor.external ρ).Equiv (FiniteTensor.external ρ') :=
    e.trans (equivOfRepresentationEq (blockTensor_comp_leviAut σ B ρ))
  intro i
  obtain ⟨h'⟩ := CuspidalInductionJacquetConstituent.nonempty_equiv_of_isSubquotient
    ((CuspidalSupport.isIrreducible_comp_mulEquiv_iff (ρ i) (entrywiseAut σ _)).mpr (hA i)) (hA i)
    (FiniteTensor.isSubquotient_factor_of_external ρ' ρ hA
      (WeylBranchPieces.IsSubquotient.of_equiv e'.symm) i)
  exact ⟨h'.symm⟩

omit [CharZero E] in
private theorem twist_inverseHalfModulus_sigma_stable (σ : E ≃ₐ[F] E) {n : ℕ} (B : BlockShape n)
    {X : Type uW} [AddCommGroup X] [Module ℂ X]
    {Ξ : Representation ℂ (B.Levi E) X} (h : IsLeviSigmaStable σ B Ξ) :
    IsLeviSigmaStable σ B (twist ((D).leviHalfModulus B)⁻¹ Ξ) := by
  obtain ⟨e⟩ := h
  let δ := (D).leviHalfModulus B
  have hδ (m : B.Levi E) : δ (leviAut σ B m) = δ m := by
    apply Units.ext
    simp only [δ, LocalFieldData.leviHalfModulus_apply, leviModulus_leviAut]
  have hc : δ⁻¹.comp (leviAut σ B).toMonoidHom = δ⁻¹ :=
    MonoidHom.ext fun m => congrArg Inv.inv (hδ m)
  refine ⟨(twistEquiv δ⁻¹ e).trans (equivOfRepresentationEq ?_)⟩
  rw [twist_comp, hc]

set_option maxHeartbeats 1200000 in
private theorem sigmaOrbitProduct_not_induced (σ : E ≃ₐ[F] E) {s n : ℕ}
    (hs : 0 < s) (hn : 0 < n) {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (P : Representation ℂ (GeneralLinear n E) W) (hi : P.IsIrreducible)
    (hsc : IsSupercuspidal P)
    (hperiod : ∀ i : ℕ, Nonempty (P.Equiv (P.comp (entrywiseAut (σ ^ i) n).toMonoidHom)) ↔ s ∣ i)
    (hprod : (sigmaOrbitProduct σ s hn P).IsIrreducible)
    (hPa : IsAdmissible (sigmaOrbitProduct σ s hn P))
    (B : BlockShape (s * n)) (hB : 2 ≤ B.length)
    {X : Type (max v uW)} [AddCommGroup X] [Module ℂ X]
    (Ξ : Representation ℂ (B.Levi E) X) (hΞ : IsSmooth Ξ) (hΞσ : IsLeviSigmaStable σ B Ξ) :
    IsEmpty ((sigmaOrbitProduct σ s hn P).Equiv
      (Induction.smoothInduced (B.parabolic E) (Ξ.comp (B.leviProjection E)))) := by
  classical
  refine ⟨fun e => ?_⟩
  let : TopologicalSpace (K).Carrier := ‹TopologicalSpace E›
  let : ValuativeRel (K).Carrier := ‹ValuativeRel E›
  let : IsNonarchimedeanLocalField (K).Carrier := ‹IsNonarchimedeanLocalField E›
  let δ := (D).leviHalfModulus B
  let ΞN := twist δ⁻¹ Ξ
  have hIi := (isIrreducible_iff_of_equiv e).mp hprod
  have hIa := (isAdmissible_iff_of_equiv e).mp hPa
  obtain ⟨hΞi, hΞa⟩ := B.isIrreducible_isAdmissible_of_smoothInduced hΞ hIi hIa
  have hΞNi : ΞN.IsIrreducible := (isIrreducible_twist_iff _ _).mpr hΞi
  have hΞNa : IsAdmissible ΞN := (isAdmissible_twist_iff _ _
    (isOpen_ker_inv ((D).isOpen_ker_leviHalfModulus B))).mpr hΞa
  obtain ⟨A₀, hAi, _, ⟨eA⟩⟩ := CuspidalSupport.padicLeviAdmissibleFactorization
    _ (K) (T) (s * n) (Nat.mul_pos hs hn) B (SmoothRep.of ΞN hΞNa.1) hΞNi hΞNa
  let A (i : Fin B.length) : SmoothRep.{0,v,max v uW} ℂ (GeneralLinear (B.size i) E) := A₀ i
  have hAσ : IsLeviSigmaStable σ B (B.blockTensor (fun i => (A i).representation)) := by
    let eσ := (twist_inverseHalfModulus_sigma_stable σ B hΞσ).some
    exact ⟨eA.symm.trans (eσ.trans (BinaryTensor.compEquiv eA (leviAut σ B).toMonoidHom))⟩
  have hN : twist ((D).parabolicHalfModulus B) (ΞN.comp (B.leviProjection E)) =
      Ξ.comp (B.leviProjection E) := by
    rw [show ΞN = twist δ⁻¹ Ξ from rfl, twist_comp]
    change twist ((D).parabolicHalfModulus B) (twist ((D).parabolicHalfModulus B)⁻¹ _) = _
    rw [twist_twist_inv]
  let eN := Induction.smoothInducedEquiv _ (equivOfRepresentationEq hN)
  let eNorm := ((D).normalizedParabolicInducedEquiv B eA).symm.trans (eN.trans e.symm)
  let ρ (k : Fin s) := P.comp (entrywiseAut (σ ^ (k : ℕ)) n).toMonoidHom
  let R (k : Fin s) : SupercuspidalRep.{v, uW} (F := E) (n := n) := by
    have hck := isSupercuspidal_comp_entrywiseAut (σ ^ (k : ℕ)) P hsc
    exact ⟨SmoothRep.of (ρ k) hck.1.1,
      (CuspidalSupport.isIrreducible_comp_mulEquiv_iff P (entrywiseAut _ _)).mpr hi, hck⟩
  let R' (k : Fin s) := (R k).universeLift.{v}
  have hR : Function.Injective (fun k => datum (E := E) hn (R' k)) := by
    intro i j h
    by_contra hij
    obtain ⟨e'⟩ := (datum_eq_iff hn (R' i) (R' j)).mp h
    exact (sigmaConjugates_pairwise_inequivalent σ P hperiod hij).false
      ((R i).universeLiftEquiv.trans (e'.trans (R j).universeLiftEquiv.symm))
  have hrotate (k : Fin s) : conjugateDatum σ (datum hn (R' k)) = datum hn (R' (finRotate s k)) := by
    rw [conjugateDatum_datum]
    apply (datum_eq_iff hn _ _).mpr
    exact ⟨(BinaryTensor.compEquiv (R k).universeLiftEquiv.symm (entrywiseAut σ n).toMonoidHom).trans
      ((sigmaConjugate_entrywiseAut_equiv_finRotate σ P hperiod k).some.trans
        (R (finRotate s k)).universeLiftEquiv)⟩
  let eR := (D).normalizedProductInducedEquiv (BlockShape.uniform s n hn)
    (fun k => (R k).universeLiftEquiv)
  exact proper_levi_not_of_sigma_stability (E := E) σ hs hn R' hR hrotate B hB A hAi
    (blockFactors_sigma_stable (E := E) σ B A hAi hAσ) (eNorm.trans eR)
    ((isIrreducible_iff_of_equiv eNorm).mpr hprod)

/-- A positive-rank unitarizable irreducible supercuspidal orbit with the prescribed period
induces a σ-discrete series on its actual normalized product carrier. -/
def UnitarySigmaOrbitDiscretenessStatement : Prop :=
  ∀ (F : Type u) [Field F] [TopologicalSpace F]
    (E : Type v) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [CharZero E] [Algebra F E] [IsModuleTopology F E]
    (σ : E ≃ₐ[F] E) (l s n : ℕ), IsCyclicAlgebra σ l → ∀ (hn : 0 < n)
    (W : Type uW) [AddCommGroup W] [Module ℂ W] (P : Representation ℂ (GeneralLinear n E) W),
    P.IsIrreducible → IsSupercuspidal P → IsUnitarizable P →
    (∀ i : ℕ, Nonempty (P.Equiv (P.comp (entrywiseAut (σ ^ i) n).toMonoidHom)) ↔ s ∣ i) →
    IsSigmaDiscreteSeries σ (s * n) (sigmaOrbitProduct σ s hn P)

/-- The orbit rotates its distinct supercuspidal classes transitively. Every block of a
σ-stable inducing Levi would have a nonempty invariant support, forcing a single block. -/
theorem unitarySigmaOrbitDiscreteness : UnitarySigmaOrbitDiscretenessStatement.{u,v,uW} := by
  intro F _ _ E _ _ _ _ _ _ _ σ l s n hcyc hn W _ _ P hi hsc hu hperiod
  have hs := (sigmaConjugate_period_pos_dvd σ P hperiod hcyc).1
  obtain ⟨hI, _, ht⟩ := sigmaOrbitProduct_isIrreducible_isUnitarizable_isTempered σ hs hn P hi hsc hu
  let : LocallyCompactSpace (GeneralLinear (s * n) E) :=
    LocalFieldTopology.generalLinear_locallyCompactSpace E (s * n)
  have hP := ht.isAdmissible
  refine ⟨hP, hI, ht, ⟨sigmaOrbitIntertwiner σ hcyc hn P hi hsc hperiod hI⟩, ?_⟩
  intro B hB X _ _ Ξ hΞ hΞσ
  exact sigmaOrbitProduct_not_induced σ hs hn P hi hsc hperiod hI hP B hB Ξ hΞ hΞσ

end Langlands.BaseChange
