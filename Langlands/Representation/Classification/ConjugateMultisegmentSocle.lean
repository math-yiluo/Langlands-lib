import Langlands.Representation.Classification.TadicBlockReductionStatement
import Langlands.Representation.Classification.SpehHermitian
import Langlands.Representation.Classification.MultisegmentConstituentContragredientProof
import Langlands.Representation.Filtration.CentralEigenspaceSplitting

/-!
# Complex conjugation of segment and multisegment socles

The complex conjugate `π̄` of a representation `π` is the same action on `ConjSpace π`.
Conjugate-linear equivariant equivalences transport the irreducible socle relation;
conjugation commutes with normalized products block by block (in the same order) and with
the real twists `ν^s`, and preserves supercuspidality. This gives the conjugate `ρ̄` of a
cuspidal datum and the conjugate `Δ̄ = [ρ̄, ν^(m-1) ρ̄]` of a segment `Δ = [ρ, ν^(m-1) ρ]`.
If `a` labels `π` (Zelevinsky socle), then `a.map Segment.conj` labels every
representation conjugate-linearly equivalent to `π`. For unitary `ρ`, `ρ̄` is the
contragredient datum `ρ̃`.
-/

noncomputable section

open CategoryTheory

namespace Langlands

universe uG uV uW uF

namespace ConjSpace

variable {G : Type uG} [Monoid G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- A conjugate-linear equivalence `V ≃ W` is a linear equivalence `V̄ ≃ W`. -/
def linearEquivOfConj (N : V ≃ₗ⋆[ℂ] W) : ConjSpace V ≃ₗ[ℂ] W :=
  (equiv V).symm.trans N

theorem linearEquivOfConj_apply (N : V ≃ₗ⋆[ℂ] W) (v : ConjSpace V) :
    linearEquivOfConj N v = N ((equiv V).symm v) := rfl

/-- A conjugate-linear equivalence intertwining `ρ` with `σ` is an equivalence of the
conjugate representation `ρ̄` with `σ`. -/
def repEquiv {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (N : V ≃ₗ⋆[ℂ] W)
    (hN : ∀ g v, N (ρ g v) = σ g (N v)) : (rep ρ).Equiv σ :=
  Representation.Equiv.mk (linearEquivOfConj N) fun g =>
    LinearMap.ext fun v => hN g ((equiv V).symm v)

/-- Conjugation of an equivalence of representations. -/
def mapEquiv {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (e : ρ.Equiv σ) :
    (rep ρ).Equiv (rep σ) :=
  repEquiv (e.toLinearEquiv.trans (equiv W)) fun g v => congrArg (equiv W)
    (Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g v)

/-- The double conjugate is the original representation. -/
def conjConjEquiv (ρ : Representation ℂ G V) : (rep (rep ρ)).Equiv ρ :=
  repEquiv (equiv V).symm fun _ _ => rfl

end ConjSpace

namespace ConjSpace

variable {G : Type uG} [Group G] {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Conjugation commutes with twisting by a real-valued character. -/
def conjTwistEquiv (χ : G →* ℂˣ) (hχ : ∀ g, starRingEnd ℂ (χ g : ℂ) = χ g)
    (ρ : Representation ℂ G V) : (rep (twist χ ρ)).Equiv (twist χ (rep ρ)) :=
  Representation.Equiv.mk (LinearEquiv.refl ℂ (ConjSpace V)) fun g => LinearMap.ext fun v => by
    change equiv V ((χ g : ℂ) • ρ g ((equiv V).symm v)) =
      (χ g : ℂ) • equiv V (ρ g ((equiv V).symm v))
    rw [map_smulₛₗ, hχ]

end ConjSpace

section ConjugateLinearTransport

variable {G : Type uG} [Group G]
  {W W' : Type uW} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

/-- Irreducibility is transported along a conjugate-linear equivariant equivalence. -/
theorem isIrreducible_of_conjEquiv {π : Representation ℂ G W} {π' : Representation ℂ G W'}
    (M : W ≃ₗ⋆[ℂ] W') (hM : ∀ g w, M (π g w) = π' g (M w)) (h : π.IsIrreducible) :
    π'.IsIrreducible :=
  (CentralEigenspaceSplitting.isIrreducible_iff_of_equiv (ConjSpace.repEquiv M hM)).mp
    ((isIrreducible_conjComp_iff π (MonoidHom.id G) Function.surjective_id).mpr h)

end ConjugateLinearTransport

namespace Classification

variable {G : Type uG} [Group G]
  {V V' W W' : Type uV} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
  [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

/-- Conjugate-linear equivariant equivalences of the ambient representation and of the
subrepresentation transport the irreducible socle relation. -/
theorem IsIrreducibleSocle.of_conjEquiv {ρ : Representation ℂ G V}
    {ρ' : Representation ℂ G V'} {π : Representation ℂ G W} {π' : Representation ℂ G W'}
    (N : V ≃ₗ⋆[ℂ] V') (hN : ∀ g v, N (ρ g v) = ρ' g (N v))
    (M : W ≃ₗ⋆[ℂ] W') (hM : ∀ g w, M (π g w) = π' g (M w))
    (h : IsIrreducibleSocle ρ π) : IsIrreducibleSocle ρ' π' := by
  obtain ⟨hπ, j, hj, huniq⟩ := h
  have hMs : ∀ g w, M.symm (π' g w) = π g (M.symm w) := by
    intro g w
    apply M.injective
    rw [LinearEquiv.apply_symm_apply, hM, LinearEquiv.apply_symm_apply]
  have hNs : ∀ g v, N.symm (ρ' g v) = ρ g (N.symm v) := by
    intro g v
    apply N.injective
    rw [LinearEquiv.apply_symm_apply, hN, LinearEquiv.apply_symm_apply]
  let j' : π'.IntertwiningMap ρ' :=
    { toFun := fun w => N (j (M.symm w))
      map_add' := fun x y => by simp
      map_smul' := fun c x => by
        rw [map_smulₛₗ, map_smul, map_smulₛₗ]
        simp
      isIntertwining' := fun g => LinearMap.ext fun w => by
        change N (j (M.symm (π' g w))) = ρ' g (N (j (M.symm w)))
        rw [hMs, j.isIntertwining, hN] }
  refine ⟨isIrreducible_of_conjEquiv M hM hπ, j', fun x y hxy => ?_, ?_⟩
  · exact M.symm.injective (hj (N.injective hxy))
  intro W'' _ _ π'' hπ'' j'' hj''
  let k : (ConjSpace.rep π'').IntertwiningMap ρ :=
    { toFun := fun w => N.symm (j'' ((ConjSpace.equiv W'').symm w))
      map_add' := fun x y => by simp
      map_smul' := fun c x => by
        rw [map_smulₛₗ, map_smul, map_smulₛₗ]
        simp
      isIntertwining' := fun g => LinearMap.ext fun w => by
        change N.symm (j'' (π'' g ((ConjSpace.equiv W'').symm w))) =
          ρ g (N.symm (j'' ((ConjSpace.equiv W'').symm w)))
        rw [j''.isIntertwining, hNs] }
  have hk : Function.Injective k := fun x y hxy =>
    (ConjSpace.equiv W'').symm.injective (hj'' (N.symm.injective hxy))
  have hirr : (ConjSpace.rep π'').IsIrreducible :=
    (isIrreducible_conjComp_iff π'' (MonoidHom.id G) Function.surjective_id).mpr hπ''
  have hrange := huniq (ConjSpace W'') (ConjSpace.rep π'') hirr k hk
  ext x
  simp only [LinearMap.mem_range]
  constructor
  · rintro ⟨w, rfl⟩
    have hmem : k (ConjSpace.equiv W'' w) ∈ LinearMap.range j.toLinearMap := by
      rw [← hrange]
      exact LinearMap.mem_range.mpr ⟨_, rfl⟩
    obtain ⟨u, hu⟩ := LinearMap.mem_range.mp hmem
    refine ⟨M u, ?_⟩
    change N (j (M.symm (M u))) = j'' w
    rw [LinearEquiv.symm_apply_apply]
    rw [show j u = N.symm (j'' w) from hu, LinearEquiv.apply_symm_apply]
  · rintro ⟨w, rfl⟩
    have hmem : j (M.symm w) ∈ LinearMap.range k.toLinearMap := by
      rw [hrange]
      exact LinearMap.mem_range.mpr ⟨_, rfl⟩
    obtain ⟨u, hu⟩ := LinearMap.mem_range.mp hmem
    refine ⟨(ConjSpace.equiv W'').symm u, ?_⟩
    change j'' ((ConjSpace.equiv W'').symm u) = N (j (M.symm w))
    rw [← show N.symm (j'' ((ConjSpace.equiv W'').symm u)) = j (M.symm w) from hu,
      LinearEquiv.apply_symm_apply]

end Classification

namespace SmoothRep

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- The complex conjugate `Ā` of a smooth representation: the same action on
`ConjSpace A`, with the same fixed vectors. -/
def conj (A : SmoothRep.{0, uG, uV} ℂ G) : SmoothRep.{0, uG, uV} ℂ G :=
  of (ConjSpace.rep A.representation) fun v => A.isSmooth v

/-- The identity of the underlying additive group, conjugate-linear from `A` to `Ā`. -/
def conjEquiv (A : SmoothRep.{0, uG, uV} ℂ G) : A ≃ₗ⋆[ℂ] A.conj :=
  ConjSpace.equiv A

theorem conjEquiv_action (A : SmoothRep.{0, uG, uV} ℂ G) (g : G) (v : A) :
    A.conjEquiv (A.representation g v) = A.conj.representation g (A.conjEquiv v) := rfl

theorem isIrreducible_conj {A : SmoothRep.{0, uG, uV} ℂ G} (h : A.IsIrreducible) :
    A.conj.IsIrreducible :=
  isIrreducible_of_conjEquiv A.conjEquiv A.conjEquiv_action h

end SmoothRep

/-- The fixed vectors of the conjugate are the same vectors. -/
theorem isAdmissible_conjRep {G : Type uG} [Group G] [TopologicalSpace G]
    {V : Type uV} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    (h : IsAdmissible ρ) : IsAdmissible (ConjSpace.rep ρ) := by
  refine ⟨fun v => h.1 v, fun K => ?_⟩
  have hfg : (fixedVectors ρ K.toSubgroup).FG := Module.Finite.iff_fg.mp (h.2 K)
  have heq : fixedVectors (ConjSpace.rep ρ) K.toSubgroup =
      (fixedVectors ρ K.toSubgroup).map (ConjSpace.equiv V).toLinearMap := by
    ext v
    constructor
    · intro hv
      exact ⟨v, hv, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact hw
  rw [heq]
  exact Module.Finite.iff_fg.mpr (hfg.map _)

namespace GeneralLinear

variable {F : Type uF} [Field F] [TopologicalSpace F] {n : ℕ}

/-- The conjugate of a supercuspidal representation is supercuspidal: its Jacquet
relations contain those of the original representation. -/
theorem isSupercuspidal_conjRep {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (GeneralLinear n F) V} (h : IsSupercuspidal ρ) :
    IsSupercuspidal (ConjSpace.rep ρ) := by
  refine ⟨isAdmissible_conjRep h.1, fun B hB g => ?_⟩
  let U := B.conjugateUnipotent g
  have hs := h.2 B hB g
  have hall : ∀ v : V, v ∈ Jacquet.relations ρ U := fun v => by
    rw [← Jacquet.mk_eq_zero]
    exact Subsingleton.elim _ _
  have hle : Jacquet.relations ρ U ≤
      (Jacquet.relations (ConjSpace.rep ρ) U).comap (ConjSpace.equiv V).toLinearMap := by
    rw [Jacquet.relations_eq_span, Submodule.span_le]
    rintro _ ⟨⟨k, v⟩, rfl⟩
    exact Jacquet.sub_mem_relations (ConjSpace.rep ρ) U k v
  have hzero : ∀ v : ConjSpace V, Jacquet.mk (ConjSpace.rep ρ) U v = 0 := fun v =>
    (Jacquet.mk_eq_zero _ _ v).mpr (hle (hall ((ConjSpace.equiv V).symm v)))
  refine ⟨fun x y => ?_⟩
  obtain ⟨v, rfl⟩ := Jacquet.mk_surjective _ _ x
  obtain ⟨w, rfl⟩ := Jacquet.mk_surjective _ _ y
  rw [hzero v, hzero w]

namespace SupercuspidalRep

/-- The complex conjugate of a supercuspidal object. -/
def conj (A : SupercuspidalRep.{uF, uV} (F := F) (n := n)) :
    SupercuspidalRep.{uF, uV} (F := F) (n := n) :=
  ⟨A.obj.conj, SmoothRep.isIrreducible_conj A.property.1,
    isSupercuspidal_conjRep A.property.2⟩

@[simp]
theorem conj_obj (A : SupercuspidalRep.{uF, uV} (F := F) (n := n)) :
    A.conj.obj = A.obj.conj := rfl

/-- Conjugation of an isomorphism of supercuspidal objects. -/
def conjIso {A B : SupercuspidalRep.{uF, uV} (F := F) (n := n)} (e : A ≅ B) :
    A.conj ≅ B.conj :=
  isoMk (SmoothRep.mkIso (ConjSpace.mapEquiv
    (SmoothRep.equivOfIso ((supercuspidalProperty (F := F) (n := n)).ι.mapIso e))))

end SupercuspidalRep

namespace SupercuspidalClass

/-- Complex conjugation of supercuspidal isomorphism classes. -/
def conj : SupercuspidalClass.{uV, uF} (F := F) (n := n) →
    SupercuspidalClass.{uV, uF} (F := F) (n := n) :=
  Quotient.map SupercuspidalRep.conj fun _ _ ⟨e⟩ => ⟨SupercuspidalRep.conjIso e⟩

@[simp]
theorem conj_isoClass (A : SupercuspidalRep.{uF, uV} (F := F) (n := n)) :
    conj A.isoClass = A.conj.isoClass := rfl

theorem conj_conj (a : SupercuspidalClass.{uV, uF} (F := F) (n := n)) : conj (conj a) = a := by
  induction a using Quotient.inductionOn with
  | h A =>
    exact Quotient.sound ⟨SupercuspidalRep.isoMk
      (SmoothRep.mkIso (ConjSpace.conjConjEquiv A.obj.representation))⟩

/-- Conjugation commutes with twisting by a real-valued character. -/
theorem conj_twist (χ : GeneralLinear n F →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set (GeneralLinear n F)))
    (hdet : (determinant : GeneralLinear n F →* Fˣ).ker ≤ χ.ker)
    (hreal : ∀ g, starRingEnd ℂ (χ g : ℂ) = χ g)
    (a : SupercuspidalClass.{uV, uF} (F := F) (n := n)) :
    conj (twist χ hχ hdet a) = twist χ hχ hdet (conj a) := by
  induction a using Quotient.inductionOn with
  | h A =>
    exact Quotient.sound ⟨SupercuspidalRep.isoMk
      (SmoothRep.mkIso (ConjSpace.conjTwistEquiv χ hreal A.obj.representation))⟩

end SupercuspidalClass

end GeneralLinear

namespace PadicField.TopologicalData

open GeneralLinear

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- The determinant power characters are real-valued. -/
theorem conj_determinantPowerCharacter (n : ℕ) (s : ℝ) (g : GeneralLinear n F.Carrier) :
    starRingEnd ℂ (T.determinantPowerCharacter n s g : ℂ) = T.determinantPowerCharacter n s g := by
  rw [coe_realPowerCharacter]
  exact Complex.conj_ofReal _

theorem supercuspidalClassConj_realPowerTwist (n : ℕ) (s : ℝ)
    (a : letI := T.topology
      GeneralLinear.SupercuspidalClass.{uV, uF} (F := F.Carrier) (n := n)) :
    letI := T.topology
    SupercuspidalClass.conj (T.supercuspidalClassRealPowerTwist n s a) =
      T.supercuspidalClassRealPowerTwist n s (SupercuspidalClass.conj a) :=
  letI := T.topology
  SupercuspidalClass.conj_twist _ _ _ (T.conj_determinantPowerCharacter n s) a

namespace CuspidalDatum

variable {T}

/-- The complex conjugate `ρ̄` of a cuspidal datum. -/
def conj (ρ : CuspidalDatum.{uV, uF} T) : CuspidalDatum.{uV, uF} T where
  rank := ρ.rank
  rank_pos := ρ.rank_pos
  cls := letI := T.topology; SupercuspidalClass.conj ρ.cls

@[simp]
theorem conj_rank (ρ : CuspidalDatum.{uV, uF} T) : ρ.conj.rank = ρ.rank := rfl

/-- `(ν^s ρ)‾ = ν^s ρ̄`. -/
theorem conj_twist (s : ℝ) (ρ : CuspidalDatum.{uV, uF} T) :
    (ρ.twist s).conj = ρ.conj.twist s := by
  obtain ⟨r, hr, a⟩ := ρ
  exact congrArg (CuspidalDatum.mk r hr) (T.supercuspidalClassConj_realPowerTwist r s a)

@[simp]
theorem conj_conj (ρ : CuspidalDatum.{uV, uF} T) : ρ.conj.conj = ρ := by
  obtain ⟨r, hr, a⟩ := ρ
  let := T.topology
  exact congrArg (CuspidalDatum.mk r hr) (SupercuspidalClass.conj_conj a)

theorem conj_injective : Function.Injective (conj : CuspidalDatum.{uV, uF} T → _) :=
  Function.LeftInverse.injective conj_conj

/-- The conjugate of a representative represents the conjugate datum. -/
theorem isRepresentedBy_conj {ρ : CuspidalDatum.{uV, uF} T}
    {A : letI := T.topology
      GeneralLinear.SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := ρ.rank)}
    (hA : ρ.IsRepresentedBy A) : ρ.conj.IsRepresentedBy (letI := T.topology; A.conj) := by
  let := T.topology
  change A.conj.isoClass = SupercuspidalClass.conj ρ.cls
  rw [← show A.isoClass = ρ.cls from hA]
  rfl

end CuspidalDatum

namespace Segment

variable {T}

/-- The conjugate segment `[ρ̄, ν^(m-1) ρ̄]`. -/
def conj (Δ : Segment.{uV, uF} T) : Segment.{uV, uF} T where
  base := Δ.base.conj
  length := Δ.length
  length_pos := Δ.length_pos

@[simp]
theorem conj_length (Δ : Segment.{uV, uF} T) : Δ.conj.length = Δ.length := rfl

@[simp]
theorem conj_degree (Δ : Segment.{uV, uF} T) : Δ.conj.degree = Δ.degree := rfl

theorem conj_member (Δ : Segment.{uV, uF} T) (i : ℕ) :
    Δ.conj.member i = (Δ.member i).conj :=
  (CuspidalDatum.conj_twist _ _).symm

theorem conj_support (Δ : Segment.{uV, uF} T) :
    Δ.conj.support = CuspidalDatum.conj '' Δ.support := by
  ext ρ
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨Δ.member i, ⟨i, hi, rfl⟩, (conj_member Δ i).symm⟩
  · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
    exact ⟨i, hi, conj_member Δ i⟩

@[simp]
theorem conj_conj (Δ : Segment.{uV, uF} T) : Δ.conj.conj = Δ := by
  obtain ⟨b, l, hl⟩ := Δ
  exact congrArg (fun b => Segment.mk b l hl) (CuspidalDatum.conj_conj b)

theorem conj_injective : Function.Injective (conj : Segment.{uV, uF} T → _) :=
  Function.LeftInverse.injective conj_conj

theorem IsLinked.conj {Δ₁ Δ₂ : Segment.{uV, uF} T} (h : Δ₁.IsLinked Δ₂) :
    Δ₁.conj.IsLinked Δ₂.conj := by
  obtain ⟨h₁, h₂, Δ, hΔ⟩ := h
  refine ⟨?_, ?_, Δ.conj, ?_⟩
  · rw [conj_support, conj_support, Set.image_subset_image_iff CuspidalDatum.conj_injective]
    exact h₁
  · rw [conj_support, conj_support, Set.image_subset_image_iff CuspidalDatum.conj_injective]
    exact h₂
  · rw [conj_support, conj_support, conj_support, hΔ, Set.image_union]

theorem Precedes.conj {Δ₁ Δ₂ : Segment.{uV, uF} T} (h : Δ₁.Precedes Δ₂) :
    Δ₁.conj.Precedes Δ₂.conj := by
  obtain ⟨hl, k, hk, hb⟩ := h
  refine ⟨hl.conj, k, hk, ?_⟩
  change Δ₂.base.conj = Δ₁.base.conj.twist (k : ℝ)
  rw [hb, CuspidalDatum.conj_twist]

theorem precedes_conj_iff (Δ₁ Δ₂ : Segment.{uV, uF} T) :
    Δ₁.conj.Precedes Δ₂.conj ↔ Δ₁.Precedes Δ₂ := by
  refine ⟨fun h => ?_, Precedes.conj⟩
  have := h.conj
  rwa [conj_conj, conj_conj] at this

end Segment

section Products

/-- Blockwise conjugate-linear equivariant equivalences give a conjugate-linear
equivariant equivalence of the normalized products, in the same order: the normalizing
half-modulus character is real. -/
theorem exists_productConjEquiv {n : ℕ} (B : BlockShape n)
    (X Y : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier)) :
    letI := T.topology
    ∀ (J : ∀ i, X i ≃ₗ⋆[ℂ] Y i),
      (∀ i g v, J i ((X i).representation g v) = (Y i).representation g (J i v)) →
      ∃ N : ((T.normalizedProductInductionFunctor B).obj X) ≃ₗ⋆[ℂ]
          ((T.normalizedProductInductionFunctor B).obj Y),
        ∀ g f, N (((T.normalizedProductInductionFunctor B).obj X).representation g f) =
          ((T.normalizedProductInductionFunctor B).obj Y).representation g (N f) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  have : IsModuleTopology (Padic p) F.Carrier := T.moduleTopology
  have : IsTopologicalRing F.Carrier := IsModuleTopology.isTopologicalRing (Padic p) F.Carrier
  intro J hJ
  let σ₁ : ∀ i : Fin B.length, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (X i) :=
    fun i => (X i).representation
  let σ₂ : ∀ i : Fin B.length, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (Y i) :=
    fun i => (Y i).representation
  let Tt : PiTensorProduct ℂ (fun i => X i) ≃ₗ⋆[ℂ] PiTensorProduct ℂ (fun i => Y i) :=
    tensorConjEquiv J
  have hlevi : ∀ (m : B.Levi F.Carrier) x,
      Tt (B.blockTensor σ₁ m x) = B.blockTensor σ₂ m (Tt x) := fun m x =>
    tensorConjEquiv_external σ₁ σ₂ J m (fun i v => hJ i (m i) v) x
  have hT : ∀ (q : B.parabolic F.Carrier) x,
      Tt (B.inducingRepresentation (T.leviHalfCharacter B) (B.blockTensor σ₁) q x) =
        B.inducingRepresentation (T.leviHalfCharacter B) (B.blockTensor σ₂) q (Tt x) := by
    intro q x
    change Tt (((T.leviHalfCharacter B).toMonoidHom (B.leviProjection F.Carrier q) : ℂ) •
        B.blockTensor σ₁ (B.leviProjection F.Carrier q) x) =
      ((T.leviHalfCharacter B).toMonoidHom (B.leviProjection F.Carrier q) : ℂ) •
        B.blockTensor σ₂ (B.leviProjection F.Carrier q) (Tt x)
    rw [map_smulₛₗ, hlevi]
    congr 1
    rw [PadicField.TopologicalData.leviHalfCharacter_toMonoidHom,
      PadicField.TopologicalData.leviHalfModulus_apply, starRingEnd_apply]
    exact Complex.conj_ofReal _
  exact ⟨Induction.smoothFunctionsConjEquiv (B.parabolic F.Carrier) Tt hT, fun g f => rfl⟩

/-- `i(Ā, νĀ, …, ν^(m-1) Ā)` is conjugate-linearly equivalent to `i(A, νA, …, ν^(m-1) A)`. -/
theorem exists_segmentInducedConj {r : ℕ}
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier))
    (m : ℕ) (hr : 0 < r) :
    letI := T.topology
    ∃ N : T.segmentInduced A m hr ≃ₗ⋆[ℂ] T.segmentInduced A.conj m hr,
      ∀ g f, N ((T.segmentInduced A m hr).representation g f) =
        (T.segmentInduced A.conj m hr).representation g (N f) := by
  let := T.topology
  refine T.exists_productConjEquiv (BlockShape.uniform m r hr) (T.segmentFactors A m hr)
    (T.segmentFactors A.conj m hr) (fun _ => A.conjEquiv) fun i g v => ?_
  change ConjSpace.equiv A ((T.determinantPowerCharacter r ((i : ℕ) : ℝ) g : ℂ) •
      A.representation g v) =
    (T.determinantPowerCharacter r ((i : ℕ) : ℝ) g : ℂ) • ConjSpace.equiv A (A.representation g v)
  rw [map_smulₛₗ]
  exact congrArg (· • ConjSpace.equiv A (A.representation g v))
    (T.conj_determinantPowerCharacter r ((i : ℕ) : ℝ) g)

end Products

variable {T}

/-- The conjugate of a segment socle is a socle of the conjugate segment. -/
theorem IsSegmentSocle.conj {Δ : Segment.{uV, uF} T}
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)}
    {π' : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.conj.degree F.Carrier)}
    (M : letI := T.topology; π ≃ₗ⋆[ℂ] π')
    (hM : letI := T.topology; ∀ g v, M (π.representation g v) = π'.representation g (M v))
    (h : T.IsSegmentSocle Δ π) : T.IsSegmentSocle Δ.conj π' := by
  let := T.topology
  obtain ⟨A, hA, hsoc⟩ := h
  refine ⟨A.conj, CuspidalDatum.isRepresentedBy_conj hA, ?_⟩
  obtain ⟨N, hN⟩ := T.exists_segmentInducedConj A.obj Δ.length Δ.rank_pos
  exact hsoc.of_conjEquiv N hN M hM

namespace SegmentProductDatum

variable {n : ℕ}

/-- Conjugate every segment and every block, keeping the order. -/
def conj (d : SegmentProductDatum.{uV, uF} T n) : SegmentProductDatum.{uV, uF} T n where
  length := d.length
  segments i := (d.segments i).conj
  degree_sum := d.degree_sum
  blocks i := letI := T.topology; (d.blocks i).conj

theorem multisegment_conj (d : SegmentProductDatum.{uV, uF} T n) :
    d.conj.multisegment = d.multisegment.map Segment.conj := by
  change ((List.ofFn fun i => (d.segments i).conj : List (Segment.{uV, uF} T)) :
      Multiset (Segment.{uV, uF} T)) =
    Multiset.map Segment.conj
      ((List.ofFn d.segments : List (Segment.{uV, uF} T)) : Multiset (Segment.{uV, uF} T))
  rw [Multiset.map_coe, List.map_ofFn]
  rfl

/-- Conjugation keeps the block shape. -/
theorem conj_shape (d : SegmentProductDatum.{uV, uF} T n) : d.conj.shape = d.shape := rfl

/-- The induced representation of the conjugate datum. -/
theorem conj_induced (d : SegmentProductDatum.{uV, uF} T n) :
    letI := T.topology
    d.conj.induced = (T.normalizedProductInductionFunctor d.shape).obj
      (fun i => (d.blocks i).conj) := rfl

theorem IsPrecedenceOrdered.conj {d : SegmentProductDatum.{uV, uF} T n}
    (h : d.IsPrecedenceOrdered) : d.conj.IsPrecedenceOrdered := by
  intro i j hij hp
  exact h i j hij ((Segment.precedes_conj_iff _ _).mp hp)

theorem HasSegmentSocles.conj {d : SegmentProductDatum.{uV, uF} T n}
    (h : d.HasSegmentSocles) : d.conj.HasSegmentSocles := by
  let := T.topology
  intro i
  exact (h i).conj (d.blocks i).conjEquiv (d.blocks i).conjEquiv_action

/-- Complex conjugation preserves the Zelevinsky socle relation: if `π` is the socle of
`i(π_1, …, π_r)`, then every `π'` conjugate-linearly equivalent to `π` is the socle of
`i(π̄_1, …, π̄_r)` for the conjugate segments, in the same order. -/
theorem IsZelevinskySocle.conj {d : SegmentProductDatum.{uV, uF} T n}
    {π π' : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (M : letI := T.topology; π ≃ₗ⋆[ℂ] π')
    (hM : letI := T.topology; ∀ g v, M (π.representation g v) = π'.representation g (M v))
    (h : d.IsZelevinskySocle π) : d.conj.IsZelevinskySocle π' := by
  let := T.topology
  refine ⟨h.1.conj, h.2.1.conj, ?_⟩
  obtain ⟨N, hN⟩ := T.exists_productConjEquiv d.shape d.blocks (fun i => (d.blocks i).conj)
    (fun i => (d.blocks i).conjEquiv) fun i => (d.blocks i).conjEquiv_action
  have hi : Classification.IsIrreducibleSocle
      ((T.normalizedProductInductionFunctor d.shape).obj d.blocks).representation
      π.representation := h.2.2
  rw [conj_induced]
  exact hi.of_conjEquiv N hN M hM

end SegmentProductDatum

/-- Conjugating every segment preserves the multisegment socle relation, for every
representation conjugate-linearly equivalent to `π`. -/
theorem Multisegment.IsZelevinskySocle.conj {n : ℕ} {a : Multisegment.{uV, uF} T}
    {π π' : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (M : letI := T.topology; π ≃ₗ⋆[ℂ] π')
    (hM : letI := T.topology; ∀ g v, M (π.representation g v) = π'.representation g (M v))
    (h : a.IsZelevinskySocle π) : Multisegment.IsZelevinskySocle (a.map Segment.conj) π' := by
  obtain ⟨d, hd, hπ⟩ := h
  exact ⟨d.conj, d.multisegment_conj.trans (congrArg _ hd), hπ.conj M hM⟩

open Classification.CuspidalProductContragredient in
/-- For a unitary cuspidal datum the conjugate is the contragredient: the invariant
positive form identifies `ρ̄` with `ρ̃`. -/
theorem CuspidalDatum.conj_eq_dualDatum {ρ : CuspidalDatum.{uV, uF} T} (hρ : ρ.IsUnitary) :
    ρ.conj = dualDatum ρ := by
  let := T.topology
  let := T.generalLinearTopologicalGroup ρ.rank
  obtain ⟨r, hr, a⟩ := ρ
  let := T.generalLinearTopologicalGroup r
  induction a using Quotient.inductionOn with
  | h A =>
    obtain ⟨b⟩ := hρ
    have hrep := dualRep_represents (ρ := ⟨r, hr, Quotient.mk _ A⟩) (A := A) rfl
    refine congrArg (CuspidalDatum.mk r hr) ?_
    refine Eq.trans ?_ hrep
    exact Quotient.sound ⟨SupercuspidalRep.isoMk (SmoothRep.mkIso (ConjSpace.repEquiv
      (b.smoothDualEquiv (GeneralLinear.compactOpen_cofinal F T r) A.property.2.1)
      fun g v => b.toSmoothDual_apply_action A.property.2.1.1 g v))⟩

end PadicField.TopologicalData

end Langlands
