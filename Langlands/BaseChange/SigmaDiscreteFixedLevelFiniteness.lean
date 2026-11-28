import Langlands.BaseChange.InducedBlockFixedLevel
import Langlands.BaseChange.SigmaDiscreteSeriesOrbitDecompositionProof
import Langlands.BaseChange.SigmaOrbitDeterminantTwist
import Langlands.BaseChange.SigmaInducedIntertwiner
import Langlands.BaseChange.TwistedPseudoCoefficientInterpolation
import Langlands.BaseChange.UnramifiedDeterminant
import Langlands.AllField.Group.GL.UnramifiedCharacterSupplement
import Langlands.AllField.Representation.Induction.BlockEquivalence
import Langlands.Representation.Category.ClassInvariants
import Langlands.Representation.CuspidalSupport.GroupTransport

/-! # A fixed-level finiteness reduction for σ-discrete series of GL -/

noncomputable section

set_option maxHeartbeats 30000
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.BaseChange

open GeneralLinear

universe u v z

variable (E : Type v) [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]

/-- The square-integrable finiteness input in ranks up to `n`, using the determinant
parameter to describe a cover by ordinary unramified twist orbits. -/
def SquareIntegrableFixedLevelTwistFiniteness (n : ℕ) : Prop :=
  ∀ (m : ℕ), 0 < m → m ≤ n →
    ∀ (J : OpenSubgroup (GeneralLinear m E)), IsCompact (J : Set (GeneralLinear m E)) →
      ∃ (r : ℕ) (Q : Fin r → SmoothRep.{0,v,z} ℂ (GeneralLinear m E)),
        (∀ i, (Q i).IsIrreducible ∧ JacquetLanglands.IsSquareIntegrable (Q i).representation) ∧
        ∀ P : SmoothRep.{0,v,z} ℂ (GeneralLinear m E), P.IsIrreducible →
          JacquetLanglands.IsSquareIntegrable P.representation →
          fixedVectors P.representation J.toSubgroup ≠ ⊥ →
          ∃ (i : Fin r) (a : ℂˣ), Nonempty (P.representation.Equiv
            (twist ((LocalFieldData.ofInstances E).determinantUnramifiedCharacter m a)
              (Q i).representation))

variable {F : Type u} [Field F] [TopologicalSpace F] [Algebra F E] [IsModuleTopology F E]

/-- The σ-discrete series visible at one open level are covered by a finite family
of invariant unramified twist orbits of σ-discrete series. -/
def HasFiniteSigmaDiscreteTwistCover (σ : E ≃ₐ[F] E) (n : ℕ)
    (K : OpenSubgroup (GeneralLinear n E)) : Prop :=
  ∃ S : Finset (SmoothRep.{0,v,z} ℂ (GeneralLinear n E)),
    (∀ R ∈ S, IsSigmaDiscreteSeries σ n R.representation) ∧
    ∀ P : SmoothRep.{0,v,z} ℂ (GeneralLinear n E), IsSigmaDiscreteSeries σ n P.representation →
      fixedVectors P.representation K.toSubgroup ≠ ⊥ →
      ∃ R ∈ S, IsUnramifiedTwistOf (entrywiseAut σ n) R.representation P.representation

private theorem ordUnits_algEquiv (σ : E ≃ₐ[F] E) (a : Eˣ) :
    (LocalFieldData.ofInstances E).ordUnits (Units.map σ.toRingHom.toMonoidHom a) =
      (LocalFieldData.ofInstances E).ordUnits a := by
  let T := LocalFieldData.ofInstances E
  let b := Units.map σ.toRingHom.toMonoidHom a
  have he : T.normalizedAbsUnits b = T.normalizedAbsUnits a :=
    normalizedAbsUnits_algEquiv σ a
  have hb : b / a ∈ T.normalizedAbsUnits.ker :=
    MonoidHom.mem_ker.mpr (by rw [map_div, he, div_self'])
  have hk : b / a ∈ T.ordUnits.ker := by rwa [T.ker_ordUnits]
  exact div_eq_one.mp (by simpa only [map_div] using MonoidHom.mem_ker.mp hk)

private theorem invariant_detUnramified (σ : E ≃ₐ[F] E) (n : ℕ) (a : ℂˣ) :
    ∀ g, (LocalFieldData.ofInstances E).determinantUnramifiedCharacter n a
        (entrywiseAut σ n g) =
      (LocalFieldData.ofInstances E).determinantUnramifiedCharacter n a g := by
  let T := LocalFieldData.ofInstances E
  intro g
  change T.unramifiedCharacter a (determinant (Matrix.GeneralLinearGroup.map σ.toRingHom g)) =
    T.unramifiedCharacter a (determinant g)
  rw [Matrix.GeneralLinearGroup.map_det]
  exact congrArg (zpowersHom ℂˣ a) (ordUnits_algEquiv E σ _)

omit [TopologicalSpace F] [IsModuleTopology F E] in
private theorem fixedLevel_seed (σ : E ≃ₐ[F] E)
    {s m n : ℕ} (hs : 0 < s) (hm : 0 < m) (h : s * m = n)
    (K : OpenSubgroup (GeneralLinear n E)) :
    ∃ J : OpenSubgroup (GeneralLinear m E), IsCompact (J : Set (GeneralLinear m E)) ∧
      ∀ (Q : SmoothRep.{0,v,z} ℂ (GeneralLinear m E)),
        fixedVectors ((sigmaOrbitProduct σ s hm Q.representation).comp
          (reindex (R := E) (finCongr h)).symm.toMonoidHom) K.toSubgroup ≠ ⊥ →
        fixedVectors Q.representation J.toSubgroup ≠ ⊥ := by
  let e := reindexContinuous (R := E) (finCongr h)
  let K' : OpenSubgroup (GeneralLinear (s * m) E) :=
    OpenSubgroup.comap e.toMulEquiv.toMonoidHom e.continuous K
  let B := BlockShape.uniform s m hm
  have hlevels : InducedBlockFixedLevelStatement.{v,z} E B K' :=
    @inducedBlockFixedLevel.{v,z} E _ _ _ _ (s * m) B K'
  unfold InducedBlockFixedLevelStatement at hlevels
  obtain ⟨J, hJ, hfix⟩ := hlevels
  let i : Fin B.length := ⟨0, hs⟩
  refine ⟨J i, hJ i, ?_⟩
  intro Q hQ
  rw [fixedVectors_comp_mulEquiv] at hQ
  have hspec := hfix (fun _ => Q)
    (fun j => Q.representation.comp (entrywiseAut (σ ^ (j : ℕ)) m).toMonoidHom) hQ i
  have he : entrywiseAut (σ ^ (i : ℕ)) m = MulEquiv.refl _ := by
    change entrywiseAut (σ ^ (0 : ℕ)) m = _
    rw [pow_zero]
    apply MulEquiv.ext
    intro g
    exact entrywiseAut_one_apply (F := F) g
  rw [he] at hspec
  exact hspec

set_option maxHeartbeats 150000 in
private theorem orbitProduct_mem_twist (σ : E ≃ₐ[F] E)
    {s m n : ℕ} (hm : 0 < m) (h : s * m = n)
    (Q Q' : SmoothRep.{0,v,z} ℂ (GeneralLinear m E)) (a : ℂˣ)
    (e : Q'.representation.Equiv
      (twist ((LocalFieldData.ofInstances E).determinantUnramifiedCharacter m a)
        Q.representation))
    (P : SmoothRep.{0,v,z} ℂ (GeneralLinear n E))
    (eP : P.representation.Equiv ((sigmaOrbitProduct σ s hm Q'.representation).comp
      (reindex (R := E) (finCongr h)).symm.toMonoidHom)) :
    IsUnramifiedTwistOf (entrywiseAut σ n)
      ((sigmaOrbitProduct σ s hm Q.representation).comp
        (reindex (R := E) (finCongr h)).symm.toMonoidHom) P.representation := by
  let T := LocalFieldData.ofInstances E
  let χ : Induction.SmoothCharacter ℂ Eˣ :=
    ⟨T.unramifiedCharacter a, T.isOpen_ker_unramifiedCharacter a⟩
  let B := BlockShape.uniform s m hm
  let f := (reindex (R := E) (finCongr h)).symm.toMonoidHom
  let ψ := T.determinantUnramifiedCharacter n a
  let ψm := T.determinantUnramifiedCharacter m a
  have hχ (j : ℕ) (b : Eˣ) :
      χ.inverse.toMonoidHom (Units.map (σ ^ j).toRingHom.toMonoidHom b) =
        χ.inverse.toMonoidHom b :=
    congrArg (fun x => (zpowersHom ℂˣ a x)⁻¹) (ordUnits_algEquiv E (σ ^ j) b)
  have hTwist := sigmaOrbitDeterminantTwist.{u,v,z,z}
  unfold SigmaOrbitDeterminantTwistStatement at hTwist
  have hAtRanks := @hTwist F ‹Field F› E ‹Field E› ‹TopologicalSpace E› ‹ValuativeRel E›
    ‹IsNonarchimedeanLocalField E› ‹Algebra F E› σ χ.inverse hχ s m n hm h
  have hAtActors := @hAtRanks Q' P inferInstance inferInstance inferInstance inferInstance
    Q'.representation P.representation
  obtain ⟨eT⟩ := hAtActors ⟨eP⟩
  have eSeed := twistEquiv ψm⁻¹ e
  rw [twist_inv_twist] at eSeed
  have eB := T.normalizedProductInducedEquiv B
    (fun j => BinaryTensor.compEquiv eSeed (entrywiseAut (σ ^ (j : ℕ)) m).toMonoidHom)
  have eFinal : (twist ψ (twist ψ⁻¹ P.representation)).Equiv
      (twist ψ ((sigmaOrbitProduct σ s hm Q.representation).comp f)) :=
    twistEquiv ψ (eT.trans (BinaryTensor.compEquiv eB f))
  rw [twist_twist_inv] at eFinal
  have hψ : IsUnramifiedCharacter ψ := by
    intro K hK g hg
    change zpowersHom ℂˣ a (determinantOrderHom E n g) = 1
    rw [determinantOrderHom_eq_one_of_mem_compact E n K hK hg, map_one]
  exact ⟨ψ, hψ, invariant_detUnramified E σ n a, ⟨eFinal⟩⟩

private theorem twistOf_of_common_base {G : Type v} [Group G] [TopologicalSpace G]
    (θ : G ≃* G) {X : Type (max v z)} [AddCommGroup X] [Module ℂ X]
    {ρ : Representation ℂ G X} {V W : Type z} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {P : Representation ℂ G V} {Q : Representation ℂ G W}
    (hP : IsUnramifiedTwistOf θ ρ P) (hQ : IsUnramifiedTwistOf θ ρ Q) :
    IsUnramifiedTwistOf θ P Q := by
  obtain ⟨χ, hχ, hiχ, ⟨eP⟩⟩ := hP
  obtain ⟨ψ, hψ, hiψ, ⟨eQ⟩⟩ := hQ
  let η := ψ * χ⁻¹
  have hη : ∀ g, η (θ g) = η g := fun g => by
    simp only [η, MonoidHom.mul_apply, MonoidHom.inv_apply, hiψ, hiχ]
  have e := twistEquiv η eP.symm
  have hcancel : η * χ = ψ := by
    apply MonoidHom.ext
    intro g
    change (ψ g * (χ g)⁻¹) * χ g = ψ g
    rw [mul_assoc, inv_mul_cancel, mul_one]
  rw [twist_twist, hcancel] at e
  exact ⟨η, hψ.mul hχ.inv, hη, ⟨eQ.trans e⟩⟩

private def HasSquareIntegrableOrbitProduct (σ : E ≃ₐ[F] E)
    {s m n : ℕ} (hm : 0 < m) (h : s * m = n)
    (P : SmoothRep.{0,v,z} ℂ (GeneralLinear n E)) : Prop :=
  ∃ Q : SmoothRep.{0,v,z} ℂ (GeneralLinear m E), Q.IsIrreducible ∧
    JacquetLanglands.IsSquareIntegrable Q.representation ∧
    Nonempty (P.representation.Equiv ((sigmaOrbitProduct σ s hm Q.representation).comp
      (reindex (R := E) (finCongr h)).symm.toMonoidHom))

private theorem fixedShape_finiteCover (σ : E ≃ₐ[F] E)
    {s m n : ℕ} (hs : 0 < s) (hm : 0 < m) (h : s * m = n)
    (K : OpenSubgroup (GeneralLinear n E))
    (hfin : SquareIntegrableFixedLevelTwistFiniteness.{v,z} E n) :
    ∃ S : Finset (SmoothRep.{0,v,z} ℂ (GeneralLinear n E)),
      (∀ R ∈ S, IsSigmaDiscreteSeries σ n R.representation) ∧
      ∀ P : SmoothRep.{0,v,z} ℂ (GeneralLinear n E),
        IsSigmaDiscreteSeries σ n P.representation →
        fixedVectors P.representation K.toSubgroup ≠ ⊥ →
        HasSquareIntegrableOrbitProduct E σ hm h P →
        ∃ R ∈ S, IsUnramifiedTwistOf (entrywiseAut σ n) R.representation P.representation := by
  classical
  obtain ⟨J, hJ, hSeed⟩ := fixedLevel_seed.{u,v,z} E σ hs hm h K
  have hmn : m ≤ n := by rw [← h]; exact Nat.le_mul_of_pos_left _ hs
  obtain ⟨r, Q, _, hQ⟩ := hfin m hm hmn J hJ
  let ρ (i : Fin r) := (sigmaOrbitProduct σ s hm (Q i).representation).comp
    (reindex (R := E) (finCongr h)).symm.toMonoidHom
  let θ := entrywiseAut σ n
  let I := {i : Fin r // ∃ P : SmoothRep.{0,v,z} ℂ (GeneralLinear n E),
    IsSigmaDiscreteSeries σ n P.representation ∧ IsUnramifiedTwistOf θ (ρ i) P.representation}
  let R (i : I) := i.property.choose
  let S : Finset (SmoothRep.{0,v,z} ℂ (GeneralLinear n E)) := Finset.univ.image R
  refine ⟨S, ?_, ?_⟩
  · rintro P hP
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hP
    exact i.property.choose_spec.1
  · intro P hP hvisible hp
    obtain ⟨A, hAi, hAsq, ⟨eP⟩⟩ := hp
    have hP' := (fixedVectors_ne_bot_iff_of_equiv eP K.toSubgroup).mp hvisible
    obtain ⟨j, a, ⟨e⟩⟩ := hQ A hAi hAsq (hSeed A hP')
    have hTw : IsUnramifiedTwistOf θ (ρ j) P.representation :=
      orbitProduct_mem_twist E σ hm h (Q j) A a e P eP
    let i : I := ⟨j, P, hP, hTw⟩
    exact ⟨R i, Finset.mem_image_of_mem _ (Finset.mem_univ i),
      twistOf_of_common_base θ i.property.choose_spec.2 hTw⟩

/-- Fixed-level finiteness for σ-discrete series follows from ordinary fixed-level
square-integrable finiteness in the possible ranks of the orbit seed. -/
def SigmaDiscreteFixedLevelFinitenessReductionStatement.{u',v',z'} : Prop :=
  ∀ (F : Type u') [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F]
    (E : Type v') [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] [Algebra F E] [IsModuleTopology F E]
    (σ : E ≃ₐ[F] E) (l n : ℕ) (K : OpenSubgroup (GeneralLinear n E)),
    IsCyclicAlgebra σ l → 0 < n → SquareIntegrableFixedLevelTwistFiniteness.{v',z'} E n →
      HasFiniteSigmaDiscreteTwistCover.{u',v',z'} E σ n K

theorem sigmaDiscreteFixedLevelFiniteness_of_squareIntegrable :
    SigmaDiscreteFixedLevelFinitenessReductionStatement.{u,v,z} := by
  classical
  intro F _ _ _ _ _ E _ _ _ _ _ _ σ l n K hcyc hn hfin
  let I := {p : Fin (n + 1) × Fin (n + 1) // p.1.val * p.2.val = n}
  let s (i : I) := i.val.1.val
  let m (i : I) := i.val.2.val
  have hpos (i : I) : 0 < s i ∧ 0 < m i := by
    have hmul : 0 < s i * m i := i.property.symm ▸ hn
    exact ⟨Nat.pos_of_ne_zero (fun h => by simp [h] at hmul),
      Nat.pos_of_ne_zero (fun h => by simp [h] at hmul)⟩
  have hshape (i : I) := fixedShape_finiteCover.{u,v,z} E σ (s := s i) (m := m i)
    (hpos i).1 (hpos i).2 i.property K hfin
  choose S hS hcover using hshape
  refine ⟨Finset.univ.biUnion S, ?_, ?_⟩
  · intro R hR
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hR
    exact hS i R hi
  · intro P hP hvisible
    have horbit := sigmaDiscreteSeriesOrbitDecomposition.{u,v,z}
    unfold SigmaDiscreteSeriesOrbitDecompositionStatement at horbit
    have hdecomp := horbit F E σ l n hcyc hn
    have hprod := hdecomp P P.representation hP
    obtain ⟨t, a, ha, hta, X, iAdd, iMod, A, hAi, hAsq, _, ⟨eP⟩⟩ := hprod
    let := iAdd
    let := iMod
    have ht : t ≤ n := Nat.le_of_dvd hn ⟨a, hta.symm⟩
    have ha' : a ≤ n := Nat.le_of_dvd hn ⟨t, by rw [mul_comm, hta]⟩
    let i : I := ⟨(⟨t, Nat.lt_succ_of_le ht⟩, ⟨a, Nat.lt_succ_of_le ha'⟩), hta⟩
    let A' := SmoothRep.of A hAsq.isAdmissible.1
    have hProd : HasSquareIntegrableOrbitProduct E σ (hpos i).2 i.property P :=
      ⟨A', hAi, hAsq, ⟨eP⟩⟩
    obtain ⟨R, hR, hTw⟩ := hcover i P hP hvisible hProd
    exact ⟨R, Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hR⟩, hTw⟩

end Langlands.BaseChange
