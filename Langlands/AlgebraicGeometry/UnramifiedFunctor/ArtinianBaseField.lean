import Langlands.AlgebraicGeometry.UnramifiedFunctor.ArtinianBaseGeneral
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.IsSepClosed

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite IsLocalRing Polynomial

open scoped TensorProduct

noncomputable section

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor.ArtinianBase

open Charts

variable {R : CommRingCat.{u}} {F : (Over (Spec R))ᵒᵖ ⥤ Type v}

section Descent

open Algebra.TensorProduct

variable {k N : Type u} [Field k] [Field N] [Algebra k N] [Algebra R k] [Algebra R N]
  [IsScalarTower R k N]

/-- Descent along a finite field extension `F₀ ⊆ N`: if any two `F₀`-embeddings `a, b` of `N`
into a field give the same restriction of `θ`, then `θ` comes from `F(Spec F₀)`. -/
lemma field_descent (hZ : ZariskiSheaf F) (hF : FaithfullyFlatSheaf F)
    (h5 : NilpotentInjective F) [FiniteDimensional k N] (F₀ : IntermediateField k N)
    [IsScalarTower R F₀ N] (θ : F.obj (op (ovR R N)))
    (hθ : ∀ (K : Type u) [Field K] [Algebra R K] (a b : N →ₐ[R] K),
      (∀ y : F₀, a y = b y) → res a θ = res b θ) :
    ∃ θ₀ : F.obj (op (ovR R F₀)), res (IsScalarTower.toAlgHom R F₀ N) θ₀ = θ := by
  have : Module.Finite F₀ N := Module.Finite.of_restrictScalars_finite k F₀ N
  have : IsArtinianRing (N ⊗[F₀] N) := IsArtinianRing.of_finite N (N ⊗[F₀] N)
  refine flatDescent hF F₀ N θ ?_
  refine eq_of_fieldAgree hZ h5 fun K _ _ ψ ↦ ?_
  rw [res_res, res_res]
  refine hθ K _ _ fun y ↦ ?_
  simp only [AlgHom.comp_apply, includeLeft_apply, AlgHom.coe_restrictScalars',
    includeRight_apply]
  congr 1
  change algebraMap F₀ N y ⊗ₜ[F₀] (1 : N) = (1 : N) ⊗ₜ[F₀] algebraMap F₀ N y
  rw [← Algebra.TensorProduct.algebraMap_apply', Algebra.TensorProduct.algebraMap_apply]

/-- Purely inseparable descent: `θ ∈ F(Spec N)` comes from any subfield `F₀` with `N / F₀`
purely inseparable (two `F₀`-embeddings of `N` into a field agree). -/
lemma purelyInseparable_descent (hZ : ZariskiSheaf F) (hF : FaithfullyFlatSheaf F)
    (h5 : NilpotentInjective F) [FiniteDimensional k N] (F₀ : IntermediateField k N)
    [IsScalarTower R F₀ N] [IsPurelyInseparable F₀ N] (θ : F.obj (op (ovR R N))) :
    ∃ θ₀ : F.obj (op (ovR R F₀)), res (IsScalarTower.toAlgHom R F₀ N) θ₀ = θ := by
  refine field_descent hZ hF h5 F₀ θ fun K _ _ a b hab ↦ ?_
  congr 1
  let : Algebra F₀ K := (a.toRingHom.comp (algebraMap F₀ N)).toAlgebra
  let a' : N →ₐ[F₀] K := { a.toRingHom with commutes' := fun _ ↦ rfl }
  let b' : N →ₐ[F₀] K := { b.toRingHom with commutes' := fun y ↦ (hab y).symm }
  have := Subsingleton.elim a' b'
  ext x
  exact congrArg (fun f : N →ₐ[F₀] K ↦ f x) this

/-- Two embeddings of a finite normal extension `N / F₀` into a field, agreeing on `F₀`, differ
by an automorphism of `N / F₀`. -/
lemma exists_conj {F₀ N K : Type*} [Field F₀] [Field N] [Field K] [Algebra F₀ N] [Normal F₀ N]
    [FiniteDimensional F₀ N] (a b : N →+* K)
    (hab : ∀ y : F₀, a (algebraMap F₀ N y) = b (algebraMap F₀ N y)) :
    ∃ g : N ≃ₐ[F₀] N, ∀ x, b x = a (g x) := by
  let : Algebra F₀ K := (a.comp (algebraMap F₀ N)).toAlgebra
  let a' : N →ₐ[F₀] K := { a with commutes' := fun _ ↦ rfl }
  let b' : N →ₐ[F₀] K := { b with commutes' := fun y ↦ (hab y).symm }
  have hmem : ∀ x, b' x ∈ a'.range := fun x ↦ by
    have := range_le_of_normal (AlgHom.id F₀ N) b a (by ext y; exact (hab y).symm) x
    obtain ⟨y, hy⟩ := this
    exact ⟨y, hy⟩
  let g₀ : N →ₐ[F₀] N := (AlgEquiv.ofInjectiveField a').symm.toAlgHom.comp
    (b'.codRestrict a'.range hmem)
  have hg₀ : ∀ x, a (g₀ x) = b x := fun x ↦ by
    have := congrArg Subtype.val
      ((AlgEquiv.ofInjectiveField a').apply_symm_apply (b'.codRestrict a'.range hmem x))
    exact this
  refine ⟨AlgEquiv.ofBijective g₀ (Algebra.IsAlgebraic.algHom_bijective g₀), fun x ↦ ?_⟩
  exact (hg₀ x).symm

/-- Galois descent: for a Galois extension `N / F₀`, an element of `F(Spec N)` invariant under
`Gal(N/F₀)` comes from `F(Spec F₀)`. -/
lemma galois_descent (hZ : ZariskiSheaf F) (hF : FaithfullyFlatSheaf F)
    (h5 : NilpotentInjective F) [FiniteDimensional k N] (F₀ : IntermediateField k N)
    [IsScalarTower R F₀ N] [IsGalois F₀ N] (θ : F.obj (op (ovR R N)))
    (hθ : ∀ g : N ≃ₐ[F₀] N, res ((g : N →ₐ[F₀] N).restrictScalars R) θ = θ) :
    ∃ θ₀ : F.obj (op (ovR R F₀)), res (IsScalarTower.toAlgHom R F₀ N) θ₀ = θ := by
  refine field_descent hZ hF h5 F₀ θ fun K _ _ a b hab ↦ ?_
  have : FiniteDimensional F₀ N := Module.Finite.of_restrictScalars_finite k F₀ N
  obtain ⟨g, hg⟩ := exists_conj (F₀ := F₀) a.toRingHom b.toRingHom hab
  have e : b = a.comp ((g : N →ₐ[F₀] N).restrictScalars R) := by
    ext x
    exact hg x
  rw [e, ← res_res, hθ g]

end Descent


section Mono

/-- `η ∈ F(Spec L)` is minimal: it does not come from a field strictly smaller than `L`. -/
def IsMinimal {L : Type u} [Field L] [Algebra R L] (η : F.obj (op (ovR R L))) : Prop :=
  ∀ (L₀ : Type u) [Field L₀] [Algebra R L₀] (j : L₀ →ₐ[R] L) (θ : F.obj (op (ovR R L₀))),
    res j θ = η → Function.Surjective j

variable {k L N : Type u} [Field k] [Algebra R k] [Field L] [Algebra k L] [Algebra R L]
  [IsScalarTower R k L] [Field N] [Algebra k N] [Algebra R N] [IsScalarTower R k N]

/-- Monomorphism on points with values in a Galois extension: a minimal `η ∈ F(Spec L)` has
distinct restrictions along distinct `k`-embeddings `L → N`, `N / k` finite Galois. The
stabilizer `H` of `θ = σ₁^* η` contains `Gal(N/σ₁ L)` and an element `g` with `g σ₁ = σ₂`;
`θ` descends to `N^H ⊆ σ₁ L`, so minimality gives `N^H = σ₁ L` and `g` fixes `σ₁ L`. -/
lemma mono_galois (hZ : ZariskiSheaf F) (hF : FaithfullyFlatSheaf F)
    (h5 : NilpotentInjective F) [FiniteDimensional k N] [IsGalois k N]
    {η : F.obj (op (ovR R L))} (hmin : IsMinimal η) (σ₁ σ₂ : L →ₐ[k] N)
    (h : res (σ₁.restrictScalars R) η = res (σ₂.restrictScalars R) η) : σ₁ = σ₂ := by
  let θ := res (σ₁.restrictScalars R) η
  let gR : (N ≃ₐ[k] N) → (N →ₐ[R] N) := fun g ↦ (g : N →ₐ[k] N).restrictScalars R
  have hmul : ∀ g g' : N ≃ₐ[k] N, gR (g * g') = (gR g).comp (gR g') := fun _ _ ↦ rfl
  have hone : gR 1 = AlgHom.id R N := rfl
  let H : Subgroup (N ≃ₐ[k] N) :=
    { carrier := {g | res (gR g) θ = θ}
      mul_mem' := fun {g g'} hg hg' ↦ by
        change res (gR (g * g')) θ = θ
        rw [hmul, ← res_res, hg', hg]
      one_mem' := by
        change res (gR 1) θ = θ
        rw [hone, res_id]
      inv_mem' := fun {g} hg ↦ by
        change res (gR g⁻¹) θ = θ
        calc res (gR g⁻¹) θ = res (gR g⁻¹) (res (gR g) θ) := by rw [hg]
          _ = res (gR (g⁻¹ * g)) θ := by rw [res_res, hmul]
          _ = θ := by rw [inv_mul_cancel, hone, res_id] }
  -- an automorphism `g₂` with `g₂ ∘ σ₁ = σ₂`
  let ϕ : σ₁.fieldRange →ₐ[k] N := σ₂.comp (σ₁.equivFieldRange).symm.toAlgHom
  let g₂₀ : N →ₐ[k] N := ϕ.liftNormal N
  have hg₂₀ : ∀ x, g₂₀ (σ₁ x) = σ₂ x := fun x ↦ by
    have := ϕ.liftNormal_commutes N (σ₁.equivFieldRange x)
    have h1 : algebraMap σ₁.fieldRange N (σ₁.equivFieldRange x) = σ₁ x := rfl
    rw [h1] at this
    exact this.trans (congrArg σ₂ ((σ₁.equivFieldRange).symm_apply_apply x))
  let g₂ : N ≃ₐ[k] N := AlgEquiv.ofBijective g₂₀ (Algebra.IsAlgebraic.algHom_bijective g₂₀)
  have hg₂ : g₂ ∈ H := by
    change res (gR g₂) (res (σ₁.restrictScalars R) η) = res (σ₁.restrictScalars R) η
    rw [res_res, h]
    congr 1
    ext x
    exact hg₂₀ x
  have hfix : σ₁.fieldRange.fixingSubgroup ≤ H := fun g hg ↦ by
    change res (gR g) θ = θ
    rw [res_res]
    congr 1
    ext x
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hg (σ₁ x) ⟨x, rfl⟩
  -- descent to `N^H`
  let F₀ := IntermediateField.fixedField H
  have : IsScalarTower R F₀ N := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  obtain ⟨θ₀, hθ₀⟩ := galois_descent hZ hF h5 F₀ θ fun g ↦ by
    have hgH : (g.restrictScalars k) ∈ H := by
      rw [← IntermediateField.fixingSubgroup_fixedField H]
      exact (IntermediateField.mem_fixingSubgroup_iff _ _).mpr fun y hy ↦ g.commutes ⟨y, hy⟩
    exact hgH
  have hF₀ : F₀ ≤ σ₁.fieldRange := by
    rw [← IsGalois.fixedField_fixingSubgroup σ₁.fieldRange]
    exact IntermediateField.fixedField_le hfix
  -- the map `F₀ → L`
  let j₀ : F₀ →ₐ[R] L := ((σ₁.equivFieldRange).symm.toAlgHom.comp
    (IntermediateField.inclusion hF₀)).restrictScalars R
  have hj₀ : (σ₁.restrictScalars R).comp j₀ = IsScalarTower.toAlgHom R F₀ N := by
    ext y
    change σ₁ ((σ₁.equivFieldRange).symm (IntermediateField.inclusion hF₀ y)) = y
    have := congrArg Subtype.val ((σ₁.equivFieldRange).apply_symm_apply
      (IntermediateField.inclusion hF₀ y))
    exact this
  have hdesc : res j₀ θ₀ = η := by
    apply fieldInj hF (σ₁.restrictScalars R)
    rw [res_res, hj₀, hθ₀]
  have hsurj := hmin F₀ j₀ θ₀ hdesc
  ext x
  obtain ⟨y, rfl⟩ := hsurj x
  have hy : (σ₁ (j₀ y) : N) = y := congrArg (fun f ↦ f y) hj₀
  have hg₂y : g₂ (y : N) = y := (IntermediateField.mem_fixedField_iff H _).mp y.2 g₂ hg₂
  rw [← hg₂₀, hy]
  exact hg₂y.symm

/-- An `R`-algebra map between `k`-algebras is `k`-linear when `R → k` is surjective. -/
def toKAlgHom {k A B : Type*} [CommRing k] [Algebra R k] [CommRing A] [Algebra k A] [Algebra R A]
    [IsScalarTower R k A] [CommRing B] [Algebra k B] [Algebra R B] [IsScalarTower R k B]
    (hk : Function.Surjective (algebraMap R k)) (σ : A →ₐ[R] B) : A →ₐ[k] B :=
  { σ.toRingHom with
    commutes' := fun t ↦ by
      obtain ⟨r, rfl⟩ := hk t
      change σ (algebraMap k A (algebraMap R k r)) = algebraMap k B (algebraMap R k r)
      rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
      exact σ.commutes r }

/-- The monomorphism property of a minimal `η ∈ F(Spec L)` on points with values in fields:
distinct `R`-embeddings of `L` into a field `K'` give distinct restrictions of `η`. Both
embeddings land, inside an algebraic closure of `K'`, in the image of a Galois closure `N` of
`L / k`, and `mono_galois` applies. -/
lemma mono_field (hZ : ZariskiSheaf F) (hF : FaithfullyFlatSheaf F) (h5 : NilpotentInjective F)
    (hk : Function.Surjective (algebraMap R k))
    (hnil : ∀ r : R, algebraMap R k r = 0 → IsNilpotent r)
    [FiniteDimensional k L] [Algebra.IsSeparable k L] {η : F.obj (op (ovR R L))}
    (hmin : IsMinimal η) {K' : Type u} [Field K'] [Algebra R K'] (σ₁ σ₂ : L →ₐ[R] K')
    (h : res σ₁ η = res σ₂ η) : σ₁ = σ₂ := by
  -- `K'` over `k`
  obtain ⟨kK, hkK⟩ := exists_factor (Algebra.ofId R k) hk (Algebra.ofId R K') (fun r hr ↦
    ((hnil r hr).map (algebraMap R K')).eq_zero)
  let : Algebra k K' := kK.toRingHom.toAlgebra
  have : IsScalarTower R k K' := IsScalarTower.of_algebraMap_eq fun r ↦
    (congrArg (fun f ↦ f r) hkK).symm
  -- a Galois closure `N` of `L / k`
  let σ₀ : L →ₐ[k] SeparableClosure k := IsSepClosed.lift
  let : Algebra L (SeparableClosure k) := σ₀.toRingHom.toAlgebra
  have : IsScalarTower k L (SeparableClosure k) :=
    IsScalarTower.of_algebraMap_eq fun t ↦ (σ₀.commutes t).symm
  let N := IntermediateField.normalClosure k L (SeparableClosure k)
  have : IsGalois k N := inferInstance
  have : FiniteDimensional k N := inferInstance
  let σN : L →ₐ[k] N := IsScalarTower.toAlgHom k L N
  let : Algebra R N := ((algebraMap k N).comp (algebraMap R k)).toAlgebra
  have : IsScalarTower R k N := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  -- a common field: the algebraic closure of `K'`
  let K'' := AlgebraicClosure K'
  have : IsScalarTower R k K'' := IsScalarTower.of_algebraMap_eq fun r ↦ by
    rw [IsScalarTower.algebraMap_apply R K' K'', IsScalarTower.algebraMap_apply R k K',
      ← IsScalarTower.algebraMap_apply k K' K'']
  have : Algebra.IsAlgebraic k N := Algebra.IsAlgebraic.of_finite k N
  let ιN : N →ₐ[k] K'' := IsAlgClosed.lift
  let ι' : K' →ₐ[k] K'' := IsScalarTower.toAlgHom k K' K''
  -- both embeddings factor through `N`
  have hfac : ∀ σ : L →ₐ[R] K', ∃ σ' : L →ₐ[k] N, ∀ x, ιN (σ' x) = ι' (σ x) := by
    intro σ
    let σk := toKAlgHom hk σ
    have hmem : ∀ x, (ι'.comp σk) x ∈ ιN.range := fun x ↦ by
      obtain ⟨n, hn⟩ := range_le_of_normal σN (ι'.comp σk).toRingHom ιN.toRingHom
        (by ext t; simp) x
      exact ⟨n, hn⟩
    refine ⟨(AlgEquiv.ofInjectiveField ιN).symm.toAlgHom.comp
      ((ι'.comp σk).codRestrict ιN.range hmem), fun x ↦ ?_⟩
    exact congrArg Subtype.val ((AlgEquiv.ofInjectiveField ιN).apply_symm_apply
      ((ι'.comp σk).codRestrict ιN.range hmem x))
  obtain ⟨σ₁', h₁⟩ := hfac σ₁
  obtain ⟨σ₂', h₂⟩ := hfac σ₂
  have e : ∀ (σ : L →ₐ[R] K') (σ' : L →ₐ[k] N), (∀ x, ιN (σ' x) = ι' (σ x)) →
      (ιN.restrictScalars R).comp (σ'.restrictScalars R) = (ι'.restrictScalars R).comp σ :=
    fun σ σ' hσ ↦ AlgHom.ext hσ
  have h' : res (σ₁'.restrictScalars R) η = res (σ₂'.restrictScalars R) η := by
    apply fieldInj hF (ιN.restrictScalars R)
    rw [res_res, res_res, e σ₁ σ₁' h₁, e σ₂ σ₂' h₂, ← res_res, ← res_res, h]
  have := mono_galois hZ hF h5 hmin σ₁' σ₂' h'
  ext x
  apply ι'.toRingHom.injective
  change ι' (σ₁ x) = ι' (σ₂ x)
  rw [← h₁, ← h₂, this]

/-- Every field point of `F` over a finite extension `κ` of `k` has a minimal field of
definition `E ⊆ κ`; it is separable over `k` (purely inseparable descent). -/
lemma exists_minimal (hZ : ZariskiSheaf F) (hF : FaithfullyFlatSheaf F)
    (h5 : NilpotentInjective F) (hk : Function.Surjective (algebraMap R k)) {κ : Type u}
    [Field κ] [Algebra k κ] [Algebra R κ] [IsScalarTower R k κ] [FiniteDimensional k κ]
    (η : F.obj (op (ovR R κ))) :
    ∃ (E : IntermediateField k κ) (θ : F.obj (op (ovR R E))),
      res (E.val.restrictScalars R) θ = η ∧ IsMinimal θ ∧ Algebra.IsSeparable k E := by
  classical
  let S : IntermediateField k κ → Prop := fun E ↦
    ∃ θ : F.obj (op (ovR R E)), res (E.val.restrictScalars R) θ = η
  have htop : S ⊤ := by
    refine ⟨res ((IntermediateField.topEquiv (F := k) (E := κ)).symm.toAlgHom.restrictScalars R) η,
      ?_⟩
    rw [res_res]
    convert res_id η using 2
    exact AlgHom.ext fun _ ↦ rfl
  have hex : ∃ n, ∃ E, S E ∧ Module.finrank k E = n := ⟨_, ⊤, htop, rfl⟩
  obtain ⟨E, hE, hEn⟩ := Nat.find_spec hex
  obtain ⟨θ, hθ⟩ := hE
  have hmin : IsMinimal θ := by
    intro L₀ _ _ j θ' hθ'
    let j' : L₀ →ₐ[R] κ := (E.val.restrictScalars R).comp j
    let E' : IntermediateField k κ := (j'.toRingHom.fieldRange).toIntermediateField (fun t ↦ by
      obtain ⟨r, rfl⟩ := hk t
      exact ⟨algebraMap R L₀ r, by
        rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes,
          ← IsScalarTower.algebraMap_apply]⟩)
    have hE'E : E' ≤ E := by
      rintro _ ⟨z, rfl⟩
      exact (j z).2
    let e : L₀ →ₐ[R] E' :=
      { toFun := fun z ↦ ⟨j' z, ⟨z, rfl⟩⟩
        map_one' := Subtype.ext (map_one j')
        map_mul' := fun a b ↦ Subtype.ext (map_mul j' a b)
        map_zero' := Subtype.ext (map_zero j')
        map_add' := fun a b ↦ Subtype.ext (map_add j' a b)
        commutes' := fun r ↦ Subtype.ext (j'.commutes r) }
    have hS' : S E' := by
      refine ⟨res e θ', ?_⟩
      rw [res_res]
      have : (E'.val.restrictScalars R).comp e = j' := AlgHom.ext fun _ ↦ rfl
      rw [this, ← res_res, hθ', hθ]
    have hle : Nat.find hex ≤ Module.finrank k E' := Nat.find_min' hex ⟨E', hS', rfl⟩
    have hEq : E' = E :=
      IntermediateField.eq_of_le_of_finrank_le hE'E (by rw [hEn]; exact hle)
    intro w
    have hw : (w : κ) ∈ E' := by
      rw [hEq]
      exact w.2
    obtain ⟨z, hz⟩ := hw
    exact ⟨z, Subtype.ext hz⟩
  refine ⟨E, θ, hθ, hmin, ?_⟩
  -- separability
  let Es := separableClosure k E
  have : IsScalarTower R Es E := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Algebra.IsAlgebraic k E := Algebra.IsAlgebraic.of_finite k E
  obtain ⟨θs, hθs⟩ := purelyInseparable_descent hZ hF h5 (k := k) (N := E) Es θ
  have hsurj := hmin Es _ θs hθs
  rw [← separableClosure.eq_top_iff, eq_top_iff]
  intro x _
  obtain ⟨y, hy⟩ := hsurj x
  rw [← hy]
  exact y.2

end Mono

end Langlands.AlgebraicGeometry.UnramifiedFunctor.ArtinianBase
