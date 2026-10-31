import Langlands.ClassFieldTheory.Local.PrimeInertiaNormStatement
import Langlands.ClassFieldTheory.Local.TotalUnramifiedCompositumProof
import Langlands.ClassFieldTheory.Local.PrimeNormBaseChangeProof
import Langlands.Galois.Local.InertiaFixedFieldUnramifiedProof
import Langlands.Galois.Local.InertiaFixedFieldBaseChangeProof
import Langlands.Galois.Local.TotalRamifiedInertiaDisjointProof

noncomputable section

namespace Langlands.LocalClassField

open Langlands.Weil.Local

universe u v

private theorem ramificationIndex_eq_of_algEquiv
    {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
    (e : F.Carrier ≃ₐ[Padic p] E.Carrier) :
    F.canonicalTopologicalData.ramificationIndex =
      E.canonicalTopologicalData.ramificationIndex := by
  have degree_one (A : PadicField.{u} p) (B : PadicField.{v} p)
      (f : A.Carrier ≃ₐ[Padic p] B.Carrier) :
      extensionDegree A B f.toAlgHom = 1 := by
    have h := finrank_mul_extensionDegree A B f.toAlgHom
    rw [← f.toLinearEquiv.finrank_eq] at h
    exact Nat.eq_of_mul_eq_mul_left (Module.finrank_pos (R := Padic p) (M := A.Carrier))
      (h.trans (mul_one _).symm)
  have hFE := PadicField.ramificationIndex_mul_extensionResidueDegree F E e.toAlgHom
  have hEF := PadicField.ramificationIndex_mul_extensionResidueDegree E F e.symm.toAlgHom
  have h1 := degree_one F E e
  have h2 : extensionDegree E F e.symm.toAlgHom = 1 := by
    have h := finrank_mul_extensionDegree E F e.symm.toAlgHom
    rw [e.toLinearEquiv.finrank_eq] at h
    exact Nat.eq_of_mul_eq_mul_left (Module.finrank_pos (R := Padic p) (M := E.Carrier))
      (h.trans (mul_one _).symm)
  rw [h1, one_mul] at hFE
  rw [h2, one_mul] at hEF
  exact Nat.dvd_antisymm ⟨_, hEF.symm⟩ ⟨_, hFE.symm⟩

private theorem unit_in_unramified_stage
    {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
    (x : (IntermediateField.fixedField
      (F.absoluteInertia F.canonicalTopologicalData))ˣ) :
    ∃ K : FiniteIntermediateExtension F.Carrier,
      ∃ _ : IsGalois F.Carrier K.field,
        F.canonicalTopologicalData.ramificationIndex =
          (K.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex ∧
        ∃ hK : K.field ≤ IntermediateField.fixedField
            (F.absoluteInertia F.canonicalTopologicalData),
          ∃ xK : K.fieldˣ,
            Units.map (IntermediateField.inclusion hK).toMonoidHom xK = x := by
  classical
  let U := IntermediateField.fixedField (F.absoluteInertia F.canonicalTopologicalData)
  obtain ⟨K, hgal, he, hmem⟩ := (PadicField.inertiaFixedFieldUnramifiedExhaustion p F).2
    {(x.val : AlgebraicClosure F.Carrier)} (by
      intro a ha
      simpa only [Finset.mem_singleton.mp ha] using x.val.property)
  let _ := hgal
  have hK : K.field ≤ U := (PadicField.inertiaFixedFieldUnramifiedExhaustion p F).1 K he
  let a : K.field := ⟨x.val, hmem _ (Finset.mem_singleton_self _)⟩
  have ha : a ≠ 0 := by
    intro hz
    apply x.ne_zero
    apply Subtype.ext
    exact congrArg (fun z : K.field => (z : AlgebraicClosure F.Carrier)) hz
  refine ⟨K, hgal, he, hK, Units.mk0 a ha, ?_⟩
  apply Units.ext
  rfl

private def rebaseFiniteExtension
    {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
    (K M : FiniteIntermediateExtension F.Carrier) (h : K.field ≤ M.field) :
    FiniteIntermediateExtension K.field := by
  let : Algebra K.field M.field := (IntermediateField.inclusion h).toAlgebra
  let : IsScalarTower F.Carrier K.field M.field :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : FiniteDimensional K.field M.field :=
    FiniteDimensional.right F.Carrier K.field M.field
  let j := (intermediateClosureEquiv F K).symm
  let E := (IntermediateField.extendScalars h).map j.toAlgHom
  exact ⟨E, Module.Finite.equiv
    (show M.field ≃ₗ[K.field] E from
      (IntermediateField.equivMap (IntermediateField.extendScalars h)
        j.toAlgHom).toLinearEquiv)⟩

private def rebaseFiniteEquiv
    {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
    (K M : FiniteIntermediateExtension F.Carrier) (h : K.field ≤ M.field) :
    letI : Algebra K.field M.field := (IntermediateField.inclusion h).toAlgebra
    M.field ≃ₐ[K.field] (rebaseFiniteExtension F K M h).field := by
  let : Algebra K.field M.field := (IntermediateField.inclusion h).toAlgebra
  exact IntermediateField.equivMap (IntermediateField.extendScalars h)
    (intermediateClosureEquiv F K).symm.toAlgHom

private theorem rebaseFiniteEquiv_apply
    {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
    (K M : FiniteIntermediateExtension F.Carrier) (h : K.field ≤ M.field)
    (z : M.field) :
    (rebaseFiniteEquiv F K M h z : AlgebraicClosure K.field) =
      (intermediateClosureEquiv F K).symm (z : AlgebraicClosure F.Carrier) := rfl

private theorem rebaseFinite_ramificationIndex
    {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
    (K M : FiniteIntermediateExtension F.Carrier) (h : K.field ≤ M.field) :
    letI := (K.asPadicField (p := p)).algebra
    letI : Module (Padic p) K.field := (K.asPadicField (p := p)).algebra.toModule
    letI := (K.asPadicField (p := p)).finiteDimensional
    (M.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex =
      ((rebaseFiniteExtension F K M h).asPadicField (p := p)).canonicalTopologicalData.ramificationIndex := by
  let : Algebra (Padic p) K.field := (K.asPadicField (p := p)).algebra
  let : Module (Padic p) K.field := (K.asPadicField (p := p)).algebra.toModule
  let : FiniteDimensional (Padic p) K.field :=
    (K.asPadicField (p := p)).finiteDimensional
  let : Algebra (Padic p) M.field := (M.asPadicField (p := p)).algebra
  let : Algebra K.field M.field := (IntermediateField.inclusion h).toAlgebra
  let : IsScalarTower (Padic p) K.field M.field :=
    IsScalarTower.of_algebraMap_eq' rfl
  let E := rebaseFiniteExtension F K M h
  let : Algebra (Padic p) E.field := (E.asPadicField (p := p)).algebra
  let : IsScalarTower (Padic p) K.field E.field :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact ramificationIndex_eq_of_algEquiv (M.asPadicField (p := p))
    (E.asPadicField (p := p)) ((rebaseFiniteEquiv F K M h).restrictScalars (Padic p))

private theorem rebaseFinite_degree
    {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
    (K M : FiniteIntermediateExtension F.Carrier) (h : K.field ≤ M.field) :
    letI : Algebra K.field M.field := (IntermediateField.inclusion h).toAlgebra
    Module.finrank K.field M.field =
      Module.finrank K.field (rebaseFiniteExtension F K M h).field := by
  let : Algebra K.field M.field := (IntermediateField.inclusion h).toAlgebra
  exact (rebaseFiniteEquiv F K M h).toLinearEquiv.finrank_eq

private theorem rebaseFinite_galois
    {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
    (K M : FiniteIntermediateExtension F.Carrier) (h : K.field ≤ M.field) :
    letI : Algebra K.field M.field := (IntermediateField.inclusion h).toAlgebra
    IsGalois K.field M.field →
      IsGalois K.field (rebaseFiniteExtension F K M h).field := by
  let : Algebra K.field M.field := (IntermediateField.inclusion h).toAlgebra
  intro hgal
  let _ := hgal
  exact IsGalois.of_algEquiv (rebaseFiniteEquiv F K M h)

private theorem finite_prime_model
    {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
    (D K : FiniteIntermediateExtension F.Carrier) [IsGalois F.Carrier D.field]
    (hprime : Nat.Prime (Module.finrank F.Carrier D.field))
    (hD : (D.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex =
      Module.finrank F.Carrier D.field * F.canonicalTopologicalData.ramificationIndex)
    (hK : (K.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex =
      F.canonicalTopologicalData.ramificationIndex) :
    ∃ M : FiniteIntermediateExtension F.Carrier,
      M.field = D.field ⊔ K.field ∧ ∃ h : K.field ≤ M.field,
        letI := (K.asPadicField (p := p)).algebra
        letI : Module (Padic p) K.field := (K.asPadicField (p := p)).algebra.toModule
        letI := (K.asPadicField (p := p)).finiteDimensional
        let E := rebaseFiniteExtension F K M h
        IsGalois K.field E.field ∧
        Nat.Prime (Module.finrank K.field E.field) ∧
        (E.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex =
          Module.finrank K.field E.field *
            (K.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex := by
  obtain ⟨_, M, hM, hDM, hKM, hdeg, hram, hgal, _⟩ := totalUnramifiedCompositum p F D K hD hK
  refine ⟨M, hM, hKM, ?_⟩
  let : Algebra (Padic p) K.field := (K.asPadicField (p := p)).algebra
  let : Module (Padic p) K.field := (K.asPadicField (p := p)).algebra.toModule
  let : FiniteDimensional (Padic p) K.field := (K.asPadicField (p := p)).finiteDimensional
  let : Algebra K.field M.field := (IntermediateField.inclusion hKM).toAlgebra
  let E := rebaseFiniteExtension F K M hKM
  have hdegE : Module.finrank K.field E.field = Module.finrank F.Carrier D.field :=
    (rebaseFinite_degree F K M hKM).symm.trans hdeg
  refine ⟨rebaseFinite_galois F K M hKM hgal, hdegE ▸ hprime, ?_⟩
  rw [← rebaseFinite_ramificationIndex F K M hKM, hram, hD, hdegE, hK]

private theorem inertia_rebase
    {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
    (K : FiniteIntermediateExtension F.Carrier)
    (hK : K.field ≤ IntermediateField.fixedField
      (F.absoluteInertia F.canonicalTopologicalData)) :
    (IntermediateField.extendScalars hK).map
        (intermediateClosureEquiv F K).symm.toAlgHom =
      IntermediateField.fixedField
        ((K.asPadicField (p := p)).absoluteInertia
          (K.asPadicField (p := p)).canonicalTopologicalData) := by
  let : Algebra F.Carrier (AlgebraicClosure K.field) :=
    ((algebraMap K.field (AlgebraicClosure K.field)).comp
      (algebraMap F.Carrier K.field)).toAlgebra
  let : SMul F.Carrier (AlgebraicClosure K.field) :=
    (inferInstance : Algebra F.Carrier (AlgebraicClosure K.field)).toSMul
  let : SMul K.field (AlgebraicClosure K.field) :=
    (inferInstance : Algebra K.field (AlgebraicClosure K.field)).toSMul
  let : IsScalarTower F.Carrier K.field (AlgebraicClosure K.field) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let j := (intermediateClosureEquiv F K).symm
  have h := PadicField.inertiaFixedFieldBaseChange p F K
    (j.toAlgHom.restrictScalars F.Carrier) (fun a => j.commutes a)
  have hs : j '' (IntermediateField.fixedField
      (F.absoluteInertia F.canonicalTopologicalData) :
      Set (AlgebraicClosure F.Carrier)) =
    ((IntermediateField.extendScalars hK).map j.toAlgHom :
      Set (AlgebraicClosure K.field)) := rfl
  change _ = IntermediateField.adjoin K.field (j '' _) at h
  rw [hs, IntermediateField.adjoin_self] at h
  exact h.symm

private theorem linearDisjoint_of_map
    {B L Ω : Type*} [Field B] [Field L] [Field Ω]
    [Algebra B L] [Algebra B Ω] (A C : IntermediateField B L)
    (f : L →ₐ[B] Ω)
    (h : (A.map f).LinearDisjoint (C.map f)) :
    A.LinearDisjoint C := by
  apply IntermediateField.linearDisjoint_iff'.mpr
  have hh := (IntermediateField.linearDisjoint_iff'.mp h).injective
  let eA := LinearEquiv.ofBijective ((f : L →ₗ[B] Ω).submoduleMap A.toSubalgebra.toSubmodule)
    ⟨fun x y hxy => Subtype.ext (f.injective (congrArg Subtype.val hxy)),
      LinearMap.submoduleMap_surjective _ _⟩
  let eC := LinearEquiv.ofBijective ((f : L →ₗ[B] Ω).submoduleMap C.toSubalgebra.toSubmodule)
    ⟨fun x y hxy => Subtype.ext (f.injective (congrArg Subtype.val hxy)),
      LinearMap.submoduleMap_surjective _ _⟩
  have ht := hh.comp (TensorProduct.congr eA eC).injective
  change Function.Injective
    (Submodule.mulMap _ _ ∘ TensorProduct.map
      ((f : L →ₗ[B] Ω).submoduleMap A.toSubalgebra.toSubmodule)
      ((f : L →ₗ[B] Ω).submoduleMap C.toSubalgebra.toSubmodule)) at ht
  rw [Submodule.coe_mulMap_comp_eq A.toSubalgebra.toSubmodule
    C.toSubalgebra.toSubmodule f] at ht
  exact ⟨ht.of_comp⟩

private theorem norm_sup_of_disjoint
    {B Ω : Type*} [Field B] [Field Ω] [Algebra B Ω]
    (A C : IntermediateField B Ω) [FiniteDimensional B C]
    (h : A.LinearDisjoint C) (x : C) :
    letI : Algebra A (A ⊔ C : IntermediateField B Ω) :=
      (IntermediateField.inclusion le_sup_left).toAlgebra
    Algebra.norm A (IntermediateField.inclusion le_sup_right x :
      (A ⊔ C : IntermediateField B Ω)) =
      algebraMap B A (Algebra.norm B x) := by
  let V := A ⊔ C
  let : Algebra A V := (IntermediateField.inclusion le_sup_left).toAlgebra
  let A' : IntermediateField B V := IntermediateField.restrict le_sup_left
  let C' : IntermediateField B V := IntermediateField.restrict le_sup_right
  let eA : A ≃ₐ[B] A' := IntermediateField.restrictAlgEquiv le_sup_left
  let eC : C ≃ₐ[B] C' := IntermediateField.restrictAlgEquiv le_sup_right
  have hA : A'.map V.val = A := IntermediateField.lift_restrict le_sup_left
  have hC : C'.map V.val = C := IntermediateField.lift_restrict le_sup_right
  have hd : A'.LinearDisjoint C' := linearDisjoint_of_map A' C' V.val (by
    rw [hA, hC]; exact h)
  have ht : A' ⊔ C' = ⊤ := by
    rw [← IntermediateField.lift_inj, IntermediateField.lift_sup,
      IntermediateField.lift_top, IntermediateField.lift_restrict le_sup_left,
      IntermediateField.lift_restrict le_sup_right]
  let : FiniteDimensional B C' := Module.Finite.equiv eC.toLinearEquiv
  let : Algebra.IsAlgebraic B C' := Algebra.IsAlgebraic.of_finite B C'
  let : Module.Free B C'.toSubalgebra :=
    Module.Free.of_basis (Module.Basis.ofVectorSpace B C')
  let : Module.Finite B C'.toSubalgebra :=
    (inferInstance : FiniteDimensional B C')
  have hs : A'.toSubalgebra ⊔ C'.toSubalgebra = ⊤ := by
    rw [← IntermediateField.sup_toSubalgebra_of_isAlgebraic_right, ht]
    rfl
  apply eA.injective
  change eA.toRingEquiv (Algebra.norm A (IntermediateField.inclusion le_sup_right x : V)) =
    eA (algebraMap B A (Algebra.norm B x))
  rw [Algebra.norm_eq_of_ringEquiv eA.toRingEquiv (by ext a; rfl),
    eA.commutes]
  change Algebra.norm A' (algebraMap C' V (eC x)) = _
  have hn := (IntermediateField.linearDisjoint_iff'.mp hd).norm_algebraMap hs (eC x)
  change Algebra.norm A' (algebraMap C' V (eC x)) =
    algebraMap B A' (Algebra.norm B (eC x)) at hn
  rw [Algebra.norm_eq_of_algEquiv eC] at hn
  exact hn

private theorem norm_sup_over_subfield
    {B Ω : Type*} [Field B] [Field Ω] [Algebra B Ω]
    (K U M : IntermediateField B Ω) [FiniteDimensional B M]
    (hKU : K ≤ U) (hKM : K ≤ M)
    (h : (IntermediateField.extendScalars hKU).LinearDisjoint
      (IntermediateField.extendScalars hKM)) (y : M) :
    letI : Algebra K M := (IntermediateField.inclusion hKM).toAlgebra
    letI : Algebra U (U ⊔ M : IntermediateField B Ω) :=
      (IntermediateField.inclusion le_sup_left).toAlgebra
    Algebra.norm U (IntermediateField.inclusion le_sup_right y :
      (U ⊔ M : IntermediateField B Ω)) =
      IntermediateField.inclusion hKU (Algebra.norm K y) := by
  let : Algebra K M := (IntermediateField.inclusion hKM).toAlgebra
  let : IsScalarTower B K M := IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional K M := FiniteDimensional.right B K M
  let A := IntermediateField.extendScalars hKU
  let C := IntermediateField.extendScalars hKM
  let : FiniteDimensional K C := (inferInstance : FiniteDimensional K M)
  let W := A ⊔ C
  let V := U ⊔ M
  let : Algebra U W := (IntermediateField.inclusion (show A ≤ W from le_sup_left)).toAlgebra
  let : Algebra U V := (IntermediateField.inclusion le_sup_left).toAlgebra
  have hW : W.restrictScalars B = V := by
    rw [← IntermediateField.restrictScalars_sup,
      IntermediateField.extendScalars_restrictScalars,
      IntermediateField.extendScalars_restrictScalars]
  let e : W ≃ₐ[U] V :=
    { toFun := fun z => ⟨z.1, (SetLike.ext_iff.mp hW z.1).mp z.2⟩
      invFun := fun z => ⟨z.1, (SetLike.ext_iff.mp hW z.1).mpr z.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_mul' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  have hn := norm_sup_of_disjoint A C h (show C from y)
  have he := Algebra.norm_eq_of_algEquiv e
    (IntermediateField.inclusion (show C ≤ W from le_sup_right) y)
  exact he.trans hn


private theorem prime_model_of_compositum
    {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
    (D K M : FiniteIntermediateExtension F.Carrier) [IsGalois F.Carrier D.field]
    (hprime : Nat.Prime (Module.finrank F.Carrier D.field))
    (hD : (D.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex =
      Module.finrank F.Carrier D.field * F.canonicalTopologicalData.ramificationIndex)
    (hK : (K.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex =
      F.canonicalTopologicalData.ramificationIndex)
    (hM : M.field = D.field ⊔ K.field) (hKM : K.field ≤ M.field) :
    letI := (K.asPadicField (p := p)).algebra
    letI : Module (Padic p) K.field := (K.asPadicField (p := p)).algebra.toModule
    letI := (K.asPadicField (p := p)).finiteDimensional
    let E := rebaseFiniteExtension F K M hKM
    IsGalois K.field E.field ∧
      (E.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex =
        Module.finrank K.field E.field *
          (K.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex := by
  obtain ⟨N, hN, hKN, hgalE, _, hramE⟩ := finite_prime_model F D K hprime hD hK
  have hNM : N = M := Subtype.ext (hN.trans hM.symm)
  subst N
  exact ⟨hgalE, hramE⟩

private theorem rebased_inertia_disjoint
    {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
    (K M : FiniteIntermediateExtension F.Carrier)
    (hKU : K.field ≤ IntermediateField.fixedField
      (F.absoluteInertia F.canonicalTopologicalData)) (hKM : K.field ≤ M.field)
    (hmodel :
      letI := (K.asPadicField (p := p)).algebra
      letI : Module (Padic p) K.field := (K.asPadicField (p := p)).algebra.toModule
      letI := (K.asPadicField (p := p)).finiteDimensional
      let E := rebaseFiniteExtension F K M hKM
      IsGalois K.field E.field ∧
        (E.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex =
          Module.finrank K.field E.field *
            (K.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex) :
    (IntermediateField.extendScalars hKU).LinearDisjoint
      (IntermediateField.extendScalars hKM) := by
  let : Algebra (Padic p) K.field := (K.asPadicField (p := p)).algebra
  let : Module (Padic p) K.field := (K.asPadicField (p := p)).algebra.toModule
  let : FiniteDimensional (Padic p) K.field := (K.asPadicField (p := p)).finiteDimensional
  let E := rebaseFiniteExtension F K M hKM
  let : IsGalois K.field E.field := hmodel.1
  apply linearDisjoint_of_map _ _ (intermediateClosureEquiv F K).symm.toAlgHom
  rw [inertia_rebase F K hKU]
  exact (PadicField.totallyRamifiedInertiaDisjoint p
    (K.asPadicField (p := p)) E hmodel.2).symm

private theorem norm_preimage_of_eq
    {B Ω : Type*} [Field B] [Field Ω] [Algebra B Ω]
    (U V W : IntermediateField B Ω) (hUV : U ≤ V) (hUW : U ≤ W)
    (hVW : V = W) (x : Uˣ)
    (hx : letI : Algebra U V := (IntermediateField.inclusion hUV).toAlgebra
      ∃ y : Vˣ, Units.map (Algebra.norm U) y = x) :
    letI : Algebra U W := (IntermediateField.inclusion hUW).toAlgebra
    ∃ y : Wˣ, Units.map (Algebra.norm U) y = x := by
  subst W
  exact hx

private theorem norm_witness_to_sup
    {B Ω : Type*} [Field B] [Field Ω] [Algebra B Ω]
    (D K U M : IntermediateField B Ω) [FiniteDimensional B D] [FiniteDimensional B M]
    (hKU : K ≤ U) (hKM : K ≤ M) (hM : M = D ⊔ K)
    (hd : (IntermediateField.extendScalars hKU).LinearDisjoint
      (IntermediateField.extendScalars hKM)) (x : Bˣ) (y : Mˣ)
    (hy : letI : Algebra K M := (IntermediateField.inclusion hKM).toAlgebra
      Algebra.norm K y.val = algebraMap B K x.val) :
    let V := U ⊔ D
    letI : Algebra U V := (IntermediateField.inclusion le_sup_left).toAlgebra
    letI : FiniteDimensional U V := finiteDimensional_sup_left U D
    ∃ z : Vˣ, normUnits U V z = Units.map (algebraMap B U).toMonoidHom x := by
  let W := U ⊔ M
  let V := U ⊔ D
  let : Algebra K M := (IntermediateField.inclusion hKM).toAlgebra
  let : Algebra U W := (IntermediateField.inclusion le_sup_left).toAlgebra
  have hWV : W = V := by
    dsimp [W, V]
    rw [hM, ← sup_assoc, sup_eq_left.mpr (le_trans hKU le_sup_left)]
  apply norm_preimage_of_eq U W V le_sup_left le_sup_left hWV
    (Units.map (algebraMap B U).toMonoidHom x)
  refine ⟨Units.map (IntermediateField.inclusion le_sup_right).toMonoidHom y, ?_⟩
  apply Units.ext
  exact (norm_sup_over_subfield K U M hKU hKM hd y.val).trans
    (congrArg (IntermediateField.inclusion hKU) hy)


private theorem base_units_are_norm
    (hbounded : PrimeNormAfterUnramifiedBaseChange.{u})
    {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
    (D : FiniteIntermediateExtension F.Carrier) [IsGalois F.Carrier D.field]
    (hprime : Nat.Prime (Module.finrank F.Carrier D.field))
    (hD : (D.asPadicField (p := p)).canonicalTopologicalData.ramificationIndex =
      Module.finrank F.Carrier D.field * F.canonicalTopologicalData.ramificationIndex)
    (x : F.Carrierˣ) :
    let U := IntermediateField.fixedField (F.absoluteInertia F.canonicalTopologicalData)
    let V := U ⊔ D.field
    letI : Algebra U V := (IntermediateField.inclusion le_sup_left).toAlgebra
    letI : FiniteDimensional U V := finiteDimensional_sup_left U D.field
    ∃ y : Vˣ, normUnits U V y = Units.map (algebraMap F.Carrier U).toMonoidHom x := by
  classical
  let U := IntermediateField.fixedField (F.absoluteInertia F.canonicalTopologicalData)
  obtain ⟨K, hgalK, hK, _, M, hM, hKM, y, hy⟩ := hbounded p F D hprime hD x
  let _ := hgalK
  have hKU : K.field ≤ U :=
    (PadicField.inertiaFixedFieldUnramifiedExhaustion p F).1 K hK.symm
  have hd := rebased_inertia_disjoint F K M hKU hKM
    (prime_model_of_compositum F D K M hprime hD hK hM hKM)
  apply norm_witness_to_sup D.field K.field U M.field hKU hKM hM hd x y
  exact congrArg Units.val hy

private theorem norm_preimage_of_equiv
    {A V A' V' : Type*} [Field A] [Field V] [Field A'] [Field V']
    [Algebra A V] [Algebra A' V']
    (eA : A ≃+* A') (eV : V ≃+* V')
    (he : (algebraMap A' V').comp eA.toRingHom = eV.toRingHom.comp (algebraMap A V))
    (x : Aˣ) (hx : ∃ y : V'ˣ,
      Units.map (Algebra.norm A') y = Units.map eA.toMonoidHom x) :
    ∃ y : Vˣ, Units.map (Algebra.norm A) y = x := by
  obtain ⟨y, hy⟩ := hx
  refine ⟨Units.map eV.symm.toMonoidHom y, ?_⟩
  apply Units.ext
  have hn := Algebra.norm_eq_of_equiv_equiv eA eV he (eV.symm y.val)
  rw [eV.apply_symm_apply] at hn
  exact hn.trans ((congrArg eA.symm (congrArg Units.val hy)).trans (eA.symm_apply_apply x.val))

private theorem norm_preimage_of_map
    {B Ω Ω' : Type*} [Field B] [Field Ω] [Field Ω'] [Algebra B Ω] [Algebra B Ω']
    (A C : IntermediateField B Ω) (f : Ω →ₐ[B] Ω') (x : Bˣ)
    (hx : let A' := A.map f
      let W' := A' ⊔ C.map f
      letI : Algebra A' W' := (IntermediateField.inclusion le_sup_left).toAlgebra
      ∃ y : W'ˣ, Units.map (Algebra.norm A') y =
        Units.map (algebraMap B A').toMonoidHom x) :
    let W := A ⊔ C
    letI : Algebra A W := (IntermediateField.inclusion le_sup_left).toAlgebra
    ∃ y : Wˣ, Units.map (Algebra.norm A) y = Units.map (algebraMap B A).toMonoidHom x := by
  let W := A ⊔ C
  let A' := A.map f
  let W' := W.map f
  let : Algebra A W := (IntermediateField.inclusion le_sup_left).toAlgebra
  let hAW : A' ≤ W' := IntermediateField.map_mono f le_sup_left
  let : Algebra A' W' := (IntermediateField.inclusion hAW).toAlgebra
  let eA := IntermediateField.equivMap A f
  let eW := IntermediateField.equivMap W f
  apply norm_preimage_of_equiv eA.toRingEquiv eW.toRingEquiv (by ext a; rfl)
  have hxe : Units.map eA.toRingEquiv.toMonoidHom (Units.map (algebraMap B A).toMonoidHom x) =
      Units.map (algebraMap B A').toMonoidHom x := by
    apply Units.ext
    exact eA.commutes x.val
  rw [hxe]
  exact norm_preimage_of_eq A' (A' ⊔ C.map f) W' le_sup_left hAW
    (IntermediateField.map_sup A C f).symm _ hx

private theorem norm_preimage_from_stage
    {B Ω : Type*} [Field B] [Field Ω] [Algebra B Ω]
    (D K U M : IntermediateField B Ω) (hKU : K ≤ U) (hKM : K ≤ M)
    (hM : M = D ⊔ K) (x : Kˣ)
    (hx : let A := IntermediateField.extendScalars hKU
      let C := IntermediateField.extendScalars hKM
      let W := A ⊔ C
      letI : Algebra A W := (IntermediateField.inclusion le_sup_left).toAlgebra
      ∃ y : Wˣ, Units.map (Algebra.norm A) y = Units.map (algebraMap K A).toMonoidHom x) :
    let V := U ⊔ D
    letI : Algebra U V := (IntermediateField.inclusion le_sup_left).toAlgebra
    ∃ y : Vˣ, Units.map (Algebra.norm U) y =
      Units.map (IntermediateField.inclusion hKU).toMonoidHom x := by
  let A := IntermediateField.extendScalars hKU
  let C := IntermediateField.extendScalars hKM
  let W := A ⊔ C
  let hUW : U ≤ W.restrictScalars B := (show A ≤ W from le_sup_left)
  have hWV : W.restrictScalars B = U ⊔ D := by
    rw [← IntermediateField.restrictScalars_sup,
      IntermediateField.extendScalars_restrictScalars,
      IntermediateField.extendScalars_restrictScalars,
      hM, ← sup_assoc, sup_eq_left.mpr (le_trans hKU le_sup_left)]
  exact norm_preimage_of_eq U (W.restrictScalars B) (U ⊔ D) hUW le_sup_left hWV _ hx

private theorem primeNormOverInertiaFixedField_of_bounded
    (hbounded : PrimeNormAfterUnramifiedBaseChange.{u}) :
    PrimeNormOverInertiaFixedField.{u} := by
  intro p _ F D _
  dsimp only
  intro hprime hD
  let U := IntermediateField.fixedField (F.absoluteInertia F.canonicalTopologicalData)
  let V := U ⊔ D.field
  let : Algebra U V := (IntermediateField.inclusion le_sup_left).toAlgebra
  intro x
  obtain ⟨K, hgalK, heK, hKU, xK, hxK⟩ := unit_in_unramified_stage F x
  let _ := hgalK
  obtain ⟨M, hM, hKM, hgalE, hprimeE, hramE⟩ :=
    finite_prime_model F D K hprime hD heK.symm
  let : Algebra (Padic p) K.field := (K.asPadicField (p := p)).algebra
  let : Module (Padic p) K.field := (K.asPadicField (p := p)).algebra.toModule
  let : FiniteDimensional (Padic p) K.field := (K.asPadicField (p := p)).finiteDimensional
  let E := rebaseFiniteExtension F K M hKM
  let : IsGalois K.field E.field := hgalE
  have hy := base_units_are_norm hbounded
    (K.asPadicField (p := p)) E hprimeE hramE xK
  change ∃ y : Vˣ, Units.map (Algebra.norm U) y = x
  rw [← hxK]
  apply norm_preimage_from_stage D.field K.field U M.field hKU hKM hM xK
  apply norm_preimage_of_map (IntermediateField.extendScalars hKU)
    (IntermediateField.extendScalars hKM) (intermediateClosureEquiv F K).symm.toAlgHom xK
  dsimp only
  rw [inertia_rebase F K hKU]
  exact hy

/-- The determinant norm to the actual canonical inertia fixed field is
surjective after adjoining a totally ramified Galois extension of prime degree. -/
theorem primeNormOverInertiaFixedField : PrimeNormOverInertiaFixedField.{u} :=
  primeNormOverInertiaFixedField_of_bounded primeNormAfterUnramifiedBaseChange

end Langlands.LocalClassField
