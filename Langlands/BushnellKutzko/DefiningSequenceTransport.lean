import Langlands.BushnellKutzko.StratumSemilinearTransport
import Langlands.BushnellKutzko.SimpleStratumGroups

/-! # Transport of defining sequences and of the groups `H^k`, `J^k` by a linear automorphism

For an `F`-linear automorphism `f` of `V`, conjugation `x ↦ f x f⁻¹` carries
`F[β]` onto `F[fβf⁻¹]`, and `f` is semilinear for this isomorphism of fields. Tame
corestrictions relative to `F[fβf⁻¹]` pull back to tame corestrictions relative to
`F[β]`, and derived strata over `F[β]` are carried to derived strata over `F[fβf⁻¹]`.
Hence the defining sequences of BK93 (2.4.2) of a stratum are carried to defining sequences
of its image, with conjugated elements. The lattices `ℌ`, `𝔍` of BK93 (3.1.7)–(3.1.8)
and the groups `H^k`, `J^k` of (3.1.14) are covariant for this conjugation.
-/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

section Derived

variable {O F V : Type*} [CommRing O] [Field F] [Algebra O F] [AddCommGroup V] [Module F V]
  [Module O V] [IsScalarTower O F V]
  {E E' : Type*} [Field E] [Field E'] [Algebra F E] [Algebra F E'] [Module E V] [Module E' V]
  [IsScalarTower F E V] [IsScalarTower F E' V]

/-- `f` as a semilinear equivalence over a field isomorphism `σK : E ≃ E'` for which it is
semilinear. -/
def semilinearOfConj (f : V ≃ₗ[F] V) (σK : E ≃+* E')
    (hfσ : ∀ (a : E) (v : V), f (a • v) = σK a • f v) : V ≃ₛₗ[(σK : E →+* E')] V where
  toFun := f
  invFun := f.symm
  map_add' := map_add f
  map_smul' := hfσ
  left_inv := f.left_inv
  right_inv := f.right_inv

omit [Algebra F E] [Algebra F E'] [IsScalarTower F E V] [IsScalarTower F E' V] in
@[simp] theorem semilinearOfConj_apply (f : V ≃ₗ[F] V) (σK : E ≃+* E')
    (hfσ : ∀ (a : E) (v : V), f (a • v) = σK a • f v) (v : V) :
    semilinearOfConj f σK hfσ v = f v :=
  rfl

omit [Algebra F E] [Algebra F E'] [IsScalarTower F E V] [IsScalarTower F E' V] in
@[simp] theorem semilinearOfConj_symm_apply (f : V ≃ₗ[F] V) (σK : E ≃+* E')
    (hfσ : ∀ (a : E) (v : V), f (a • v) = σK a • f v) (v : V) :
    (semilinearOfConj f σK hfσ).symm v = f.symm v :=
  rfl

theorem endConj_restrictScalars (f : V ≃ₗ[F] V) (σK : E ≃+* E')
    (hfσ : ∀ (a : E) (v : V), f (a • v) = σK a • f v) (b : Module.End E V) :
    endConj f (b.restrictScalars F) =
      (endConj (semilinearOfConj f σK hfσ) b).restrictScalars F := by
  ext w
  rfl

/-- The hypothesis that the image of a lattice chain normalized by `Eˣ` is normalized by
`E'ˣ`. -/
def NormalizationTransports (O : Type*) [CommRing O] [Algebra O F] [Module O V]
    [IsScalarTower O F V] (f : V ≃ₗ[F] V) (E E' : Type*) [Field E] [Field E'] [Algebra F E]
    [Algebra F E'] [Module E V] [Module E' V] [IsScalarTower F E V] [IsScalarTower F E' V] :
    Prop :=
  ∀ L L' : LatticeChain O F V, L.Corresponds f L' →
    (∀ a : Eˣ, subfieldUnits F E V a ∈ L.stabilizer) →
      ∀ a : E'ˣ, subfieldUnits F E' V a ∈ L'.stabilizer

/-- The pullback `x ↦ f⁻¹ s'(f x f⁻¹) f` of a tame corestriction relative to `E'`. -/
def TameCorestriction.pullback (f : V ≃ₗ[F] V) (σK : E ≃+* E')
    (hfσ : ∀ (a : E) (v : V), f (a • v) = σK a • f v)
    (hnorm : NormalizationTransports O f E E') (s' : TameCorestriction O F E' V) :
    TameCorestriction O F E V where
  toFun x := endConj (semilinearOfConj f σK hfσ).symm (s' (endConj f x))
  map_zero' := by simp
  map_add' x y := by simp
  map_mul_left b x := by
    have h1 : s'.toAddMonoidHom ((endConj (semilinearOfConj f σK hfσ) b).restrictScalars F *
        endConj f x) = endConj (semilinearOfConj f σK hfσ) b * s'.toAddMonoidHom (endConj f x) :=
      s'.map_mul_left _ _
    rw [map_mul, endConj_restrictScalars f σK hfσ, h1, map_mul, endConj_symm_endConj]
  map_mul_right x b := by
    have h1 : s'.toAddMonoidHom (endConj f x *
        (endConj (semilinearOfConj f σK hfσ) b).restrictScalars F) =
        s'.toAddMonoidHom (endConj f x) * endConj (semilinearOfConj f σK hfσ) b :=
      s'.map_mul_right _ _
    rw [map_mul, endConj_restrictScalars f σK hfσ, h1, map_mul, endConj_symm_endConj]
  image_order L hL := by
    let L' := L.transport f (σO := RingHom.id O) (fun _ => rfl)
    have hLL' : L.Corresponds f L' := L.corresponds_transport f _
    have himage : (s'.toAddMonoidHom : Module.End F V → Module.End E' V) ''
        (L'.order : Set (Module.End F V)) =
        {b : Module.End E' V | b.restrictScalars F ∈ L'.order} :=
      s'.image_order L' (hnorm L L' hLL' hL)
    ext b
    simp only [Set.mem_image, Set.mem_ofPred_eq, SetLike.mem_coe]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hmem : s' (endConj f x) ∈ s' '' (L'.order : Set (Module.End F V)) :=
        ⟨_, (hLL'.mem_order x).2 hx, rfl⟩
      rw [himage] at hmem
      rw [← hLL'.mem_order, endConj_restrictScalars f σK hfσ, endConj_endConj_symm]
      exact hmem
    · intro hb
      have hmem : endConj (semilinearOfConj f σK hfσ) b ∈
          s' '' (L'.order : Set (Module.End F V)) := by
        rw [himage]
        change (endConj (semilinearOfConj f σK hfσ) b).restrictScalars F ∈ L'.order
        rw [← endConj_restrictScalars f σK hfσ, hLL'.mem_order]
        exact hb
      obtain ⟨y, hy, hys⟩ := hmem
      refine ⟨endConj f.symm y, ?_, ?_⟩
      · rw [← hLL'.mem_order, endConj_endConj_symm]
        exact hy
      · rw [endConj_endConj_symm, hys, endConj_symm_endConj]

variable [Algebra O E] [Algebra O E'] [IsScalarTower O F E] [IsScalarTower O F E']

/-- The restriction of `σK` to the integral closures of `O`. -/
def integralClosureConj (σK : E ≃+* E') (hσO : ∀ o : O, σK (algebraMap O E o) = algebraMap O E' o) :
    integralClosure O E ≃+* integralClosure O E' :=
  (AlgEquiv.mapIntegralClosure (R := O) (A := E) (S := E')
    { σK with commutes' := hσO }).toRingEquiv

@[simp] theorem coe_integralClosureConj (σK : E ≃+* E')
    (hσO : ∀ o : O, σK (algebraMap O E o) = algebraMap O E' o) (x : integralClosure O E) :
    ((integralClosureConj σK hσO x : integralClosure O E') : E') = σK x :=
  rfl

omit [IsScalarTower O F E] [IsScalarTower O F E'] in
theorem derivedEquivalentToSimple_transport (f : V ≃ₗ[F] V) (σK : E ≃+* E')
    (hfσ : ∀ (a : E) (v : V), f (a • v) = σK a • f v)
    (hσO : ∀ o : O, σK (algebraMap O E o) = algebraMap O E' o)
    (hnorm : NormalizationTransports O f E E')
    {S S' : Stratum O F V} (hS : S.Corresponds f S') (hgen : S'.IsGeneratedField E')
    {b : Module.End F V} (s' : TameCorestriction O F E' V)
    (h : S.DerivedEquivalentToSimple E b (TameCorestriction.pullback f σK hfσ hnorm s')) :
    S'.DerivedEquivalentToSimple E' (endConj f b) s' := by
  obtain ⟨D, C, ⟨hSs, -, hb, hDS, hDn, hDr, hDb⟩, hCD, hCn, hCr, hDC, hC⟩ := h
  let fE := semilinearOfConj f σK hfσ
  let σO := integralClosureConj σK hσO
  have hσ : ∀ o : integralClosure O E, (σK : E →+* E') (algebraMap (integralClosure O E) E o) =
      algebraMap (integralClosure O E') E' ((σO : integralClosure O E →+* integralClosure O E') o) :=
    fun _ => rfl
  let DL := D.chain.transport (σ := (σK : E →+* E')) (σO := (σO : integralClosure O E →+*
    integralClosure O E')) fE hσ
  have hDL : D.chain.Corresponds fE DL := D.chain.corresponds_transport fE hσ
  let D' := D.transport fE DL hDL
  have hD : D.Corresponds fE D' := D.corresponds_transport fE DL hDL
  have hCL : C.chain.Corresponds fE DL := hCD ▸ hDL
  let C' := C.transport fE DL hCL
  have hC' : C.Corresponds fE C' := C.corresponds_transport fE DL hCL
  refine ⟨D', C', ⟨(hS.isSimple_iff).2 hSs, hgen, ?_, ?_, ?_, ?_, ?_⟩, rfl, ?_, ?_, ?_, ?_⟩
  · rw [hS.r, hS.chain.mem_endFiltration]
    exact hb
  · intro i
    ext w
    change w ∈ DL.lattice i ↔ w ∈ S'.chain.lattice i
    rw [hS.chain.symm i w, hDL.symm i w]
    change f.symm w ∈ D.chain.lattice i ↔ _
    rw [← SetLike.mem_coe, hDS i, SetLike.mem_coe]
  · change D.n = S'.r
    rw [hDn, hS.r]
  · change D.r = S'.r - 1
    rw [hDr, hS.r]
  · change endConj fE D.b = s' (endConj f b)
    rw [hDb]
    change endConj fE (endConj fE.symm (s' (endConj f b))) = _
    rw [endConj_endConj_symm]
  · exact hCn
  · exact hCr
  · exact (hD.equivalent_iff hC').2 hDC
  · exact (hC'.isSimple_iff).2 hC

end Derived

/-! ### The generated field and its conjugate -/

section Base

variable {O F V : Type*} [CommRing O] [Field F] [Algebra O F] [AddCommGroup V] [Module F V]
  [Module O V] [IsScalarTower O F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

theorem Stratum.isGeneratedField_elementAlgebra (β : A) (h : IsField (elementAlgebra β))
    (S : Stratum O F V) (hS : S.b = β) :
    letI := h.toField
    S.IsGeneratedField (elementAlgebra β) := by
  let := h.toField
  refine ⟨⟨β, Algebra.self_mem_adjoin_singleton F β⟩, ?_, ?_⟩
  · rw [hS]
    exact LinearMap.ext fun _ => rfl
  · apply Subalgebra.map_injective (f := (elementAlgebra β).val) Subtype.val_injective
    rw [AlgHom.map_adjoin, Set.image_singleton, Algebra.map_top, Subalgebra.range_val]
    rfl

theorem elementAlgebraConj_smul (f : V ≃ₗ[F] V) (β : A) (a : elementAlgebra β) (v : V) :
    f (a • v) = elementAlgebraConj f β a • f v := by
  change f ((a : A) v) = endConj f (a : A) (f v)
  rw [endConj_apply_apply]

theorem elementAlgebraConj_algebraMap (f : V ≃ₗ[F] V) (β : A) (o : O) :
    elementAlgebraConj f β (algebraMap O (elementAlgebra β) o) =
      algebraMap O (elementAlgebra (endConj f β)) o := by
  apply Subtype.ext
  change endConj f (algebraMap O A o) = algebraMap O A o
  rw [IsScalarTower.algebraMap_apply O F A, endConj_algebraMap]
  rfl

theorem coe_subfieldUnits_elementAlgebra (β : A) (h : IsField (elementAlgebra β)) :
    letI := h.toField
    ∀ a : (elementAlgebra β)ˣ,
      ((subfieldUnits F (elementAlgebra β) V a : G) : A) = ((a : elementAlgebra β) : A) := by
  intro a
  exact LinearMap.ext fun _ => rfl

theorem normalizationTransports_elementAlgebra (f : V ≃ₗ[F] V) (β : A)
    (h : IsField (elementAlgebra β)) (h' : IsField (elementAlgebra (endConj f β))) :
    letI := h.toField
    letI := h'.toField
    NormalizationTransports O f (elementAlgebra β) (elementAlgebra (endConj f β)) := by
  let := h.toField
  let := h'.toField
  intro L L' hL hnorm a'
  let a : (elementAlgebra β)ˣ := Units.map ((elementAlgebraConj f β).symm : elementAlgebra
    (endConj f β) →* elementAlgebra β) a'
  have heq : subfieldUnits F (elementAlgebra (endConj f β)) V a' =
      unitsConj f (subfieldUnits F (elementAlgebra β) V a) := by
    apply Units.ext
    rw [coe_subfieldUnits_elementAlgebra _ h', coe_unitsConj,
      coe_subfieldUnits_elementAlgebra _ h]
    change _ = ((elementAlgebraConj f β ((elementAlgebraConj f β).symm (a' : elementAlgebra
      (endConj f β))) : elementAlgebra (endConj f β)) : A)
    rw [RingEquiv.apply_symm_apply]
  rw [heq, hL.mem_stabilizer]
  exact hnorm a

theorem Stratum.Corresponds.hasSimpleDerivedStratum (f : V ≃ₗ[F] V) {S S' : Stratum O F V}
    (hS : S.Corresponds f S') {b : A} (h : S.HasSimpleDerivedStratum b) :
    S'.HasSimpleDerivedStratum (endConj f b) := by
  obtain ⟨c', n', r', b', hrn, hv⟩ := S'
  obtain ⟨hc, hn, hr, hb⟩ := hS
  change b' = endConj f S.b at hb
  subst hb
  intro h' s'
  have hE : IsField (elementAlgebra S.b) := (isField_elementAlgebra_endConj_iff f S.b).1 h'
  let := hE.toField
  let := h'.toField
  have hnorm := normalizationTransports_elementAlgebra (O := O) f S.b hE h'
  have hd := h hE (TameCorestriction.pullback f (elementAlgebraConj f S.b)
    (elementAlgebraConj_smul f S.b) hnorm s')
  exact derivedEquivalentToSimple_transport f (elementAlgebraConj f S.b)
    (elementAlgebraConj_smul f S.b) (elementAlgebraConj_algebraMap f S.b) hnorm
    ⟨hc, hn, hr, rfl⟩
    (Stratum.isGeneratedField_elementAlgebra (endConj f S.b) h' _ rfl) s' hd

/-! ### Defining sequences -/

theorem Stratum.Corresponds.isDefiningSequence (f : V ≃ₗ[F] V) {S S' : Stratum O F V}
    (hS : S.Corresponds f S') {s : ℕ} {q q' : Fin (s + 1) → Stratum O F V}
    (hq : ∀ i, (q i).Corresponds f (q' i)) (h : S.IsDefiningSequence q) :
    S'.IsDefiningSequence q' := by
  obtain ⟨hPure, hTerms, hEq, hr0, hMono, hStep, hLast, hDerived⟩ := h
  have hr : (fun i => (q' i).r) = fun i => (q i).r := funext fun i => (hq i).r
  refine ⟨hS.isPure_iff.2 hPure, fun i => ⟨?_, ?_, (hq i).isSimple_iff.2 (hTerms i).2.2⟩,
    ((hq 0).equivalent_iff hS).2 hEq, by rw [(hq 0).r, hS.r, hr0], by rw [hr]; exact hMono,
    fun i => ⟨?_, ?_⟩, ?_, fun i => ?_⟩
  · exact ((hq i).chain.order_eq_iff hS.chain).2 (hTerms i).1
  · rw [(hq i).n, hS.n, (hTerms i).2.1]
  · rw [(hq i.castSucc).b, hS.chain.criticalExponent_eq, (hq i.succ).r]
    exact (hStep i).1
  · rw [(hq i.succ).b, (hq i.castSucc).b, ← map_sub, (hq i.succ).r, hS.chain.mem_endFiltration]
    exact (hStep i).2
  · rw [(hq (Fin.last s)).b, hS.chain.criticalExponent_eq, hS.n]
    exact hLast
  · rw [(hq i.succ).b, (hq i.castSucc).b, ← map_sub]
    exact (hq i.succ).hasSimpleDerivedStratum f (hDerived i)

/-- The image of a defining sequence under `f`: its terms are the images of the terms. -/
def Stratum.DefiningSequenceChoice.transport (f : V ≃ₗ[F] V) {S S' : Stratum O F V}
    (hS : S.Corresponds f S') (q : S.DefiningSequenceChoice) : S'.DefiningSequenceChoice where
  steps := q.steps
  terms i := (q.terms i).transport f ((q.terms i).chain.transport f (σO := RingHom.id O)
    (fun _ => rfl)) ((q.terms i).chain.corresponds_transport f _)
  isDefiningSequence := hS.isDefiningSequence f (fun i => Stratum.corresponds_transport _ _ _ _)
    q.isDefiningSequence
  firstElement := by
    change endConj f (q.terms 0).b = S'.b
    rw [q.firstElement, hS.b]

@[simp] theorem Stratum.DefiningSequenceChoice.tail_transport (f : V ≃ₗ[F] V)
    {S S' : Stratum O F V} (hS : S.Corresponds f S') (q : S.DefiningSequenceChoice) :
    (q.transport f hS).tail = q.tail.map (endConj f) := by
  simp only [Stratum.DefiningSequenceChoice.tail, List.map_ofFn]
  rfl

/-! ### The lattices and groups of a simple stratum -/

theorem LatticeChain.Corresponds.simpleCriticalDepth_eq {f : V ≃ₗ[F] V}
    {L L' : LatticeChain O F V} (hL : L.Corresponds f L') (β : A) :
    simpleCriticalDepth L' (endConj f β) = simpleCriticalDepth L β := by
  unfold simpleCriticalDepth
  rw [hL.criticalExponent_eq]

theorem LatticeChain.Corresponds.finiteCriticalDepth_eq {f : V ≃ₗ[F] V}
    {L L' : LatticeChain O F V} (hL : L.Corresponds f L') (n : ℤ) (β : A) :
    finiteCriticalDepth L' n (endConj f β) = finiteCriticalDepth L n β := by
  unfold finiteCriticalDepth
  rw [hL.simpleCriticalDepth_eq]

theorem LatticeChain.Corresponds.mem_simpleStratumLattices {f : V ≃ₗ[F] V}
    {L L' : LatticeChain O F V} (hL : L.Corresponds f L') (n : ℤ) (tail : List A) :
    ∀ β : A,
      (∀ x, endConj f x ∈ (simpleStratumLattices L' n (endConj f β) (tail.map (endConj f))).1 ↔
        x ∈ (simpleStratumLattices L n β tail).1) ∧
      (∀ x, endConj f x ∈ (simpleStratumLattices L' n (endConj f β) (tail.map (endConj f))).2 ↔
        x ∈ (simpleStratumLattices L n β tail).2) := by
  induction tail with
  | nil =>
    intro β
    exact ⟨mem_sup_of_corresponds (endConj f).toAddEquiv (fun x => hL.mem_centralizerLattice x)
        (fun x => hL.mem_endFiltration x),
      mem_sup_of_corresponds (endConj f).toAddEquiv (fun x => hL.mem_centralizerLattice x)
        (fun x => hL.mem_endFiltration x)⟩
  | cons γ tail ih =>
    intro β
    simp only [List.map_cons, simpleStratumLattices, hL.finiteCriticalDepth_eq]
    refine ⟨mem_sup_of_corresponds (endConj f).toAddEquiv (fun x => hL.mem_centralizerLattice x)
        (fun x => ?_), mem_sup_of_corresponds (endConj f).toAddEquiv
        (fun x => hL.mem_centralizerLattice x) (fun x => ?_)⟩
    · change _ ∈ _ ⊓ _ ↔ _ ∈ _ ⊓ _
      rw [Submodule.mem_inf, Submodule.mem_inf]
      exact and_congr ((ih γ).1 x) (hL.mem_endFiltration x)
    · change _ ∈ _ ⊓ _ ↔ _ ∈ _ ⊓ _
      rw [Submodule.mem_inf, Submodule.mem_inf]
      exact and_congr ((ih γ).2 x) (hL.mem_endFiltration x)

theorem LatticeChain.Corresponds.simpleHGroup_eq {f : V ≃ₗ[F] V}
    {L L' : LatticeChain O F V} (hL : L.Corresponds f L') (n : ℤ) (β : A) (tail : List A)
    (m : ℕ) :
    simpleHGroup L' n (endConj f β) (tail.map (endConj f)) m =
      (simpleHGroup L n β tail m).map (unitsConj f).toMonoidHom := by
  unfold simpleHGroup
  rw [MonoidHom.map_closure]
  congr 1
  ext u'
  obtain ⟨u, rfl⟩ := (unitsConj f).surjective u'
  change _ ↔ (unitsConj f) u ∈ (unitsConj f) '' _
  rw [(unitsConj f).injective.mem_set_image]
  change unitsConj f u ∈ L'.unitFiltration m ∧ endConj f u ∈ simpleHLattice L' n _ _ ↔
    u ∈ L.unitFiltration m ∧ (u : A) ∈ simpleHLattice L n β tail
  rw [hL.mem_unitFiltration, ((hL.mem_simpleStratumLattices n tail β).1 u)]

theorem LatticeChain.Corresponds.simpleJGroup_eq {f : V ≃ₗ[F] V}
    {L L' : LatticeChain O F V} (hL : L.Corresponds f L') (n : ℤ) (β : A) (tail : List A)
    (m : ℕ) :
    simpleJGroup L' n (endConj f β) (tail.map (endConj f)) m =
      (simpleJGroup L n β tail m).map (unitsConj f).toMonoidHom := by
  unfold simpleJGroup
  rw [MonoidHom.map_closure]
  congr 1
  ext u'
  obtain ⟨u, rfl⟩ := (unitsConj f).surjective u'
  change _ ↔ (unitsConj f) u ∈ (unitsConj f) '' _
  rw [(unitsConj f).injective.mem_set_image]
  change unitsConj f u ∈ L'.unitFiltration m ∧ endConj f u ∈ simpleJLattice L' n _ _ ↔
    u ∈ L.unitFiltration m ∧ (u : A) ∈ simpleJLattice L n β tail
  rw [hL.mem_unitFiltration, ((hL.mem_simpleStratumLattices n tail β).2 u)]

end Base

end Langlands.BushnellKutzko
