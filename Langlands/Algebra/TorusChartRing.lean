import Langlands.Algebra.TorusChartAlgebra
import Langlands.Algebra.HopfPointClosedLocus
import Langlands.Algebra.HopfPointRigidity
import Langlands.Algebra.HopfPointConnected

/-! # Ring-level data of a torus chart -/

noncomputable section

universe u

open TensorProduct

namespace Langlands.Algebra.TorusChartRing

open HopfPointExtension HopfPointBridge HopfPointTwist FiniteBialgebraHom TorusChartAlgebra
  HopfPointClosedLocus LatticeConfiguration InvariantPrincipalOpen HopfPointRigidity

variable (R : Type u) [CommRing R] (A : Type u) [CommRing A] [HopfAlgebra R A]
  [Algebra.FinitePresentation R A] (r : Type u) [Fintype r] [DecidableEq r] (m : ℕ) [NeZero m]

/-- The twisting group `Aut((ℤ/m)^r)`, written multiplicatively. -/
abbrev Γ : Type u := Multiplicative (AddAut (r → ZMod m))

/-- The twisting group is finite. -/
instance {r : Type u} [Fintype r] [DecidableEq r] {m : ℕ} [NeZero m] : Finite (Γ r m) := by
  change Finite (Multiplicative ((r → ZMod m) ≃+ (r → ZMod m)))
  have : Finite ((r → ZMod m) ≃+ (r → ZMod m)) :=
    Finite.of_injective (fun e : (r → ZMod m) ≃+ (r → ZMod m) => (e : (r → ZMod m) → r → ZMod m))
      (fun a b h => AddEquiv.ext (congrFun h))
  infer_instance

/-- The twisting action of `Γ` on the representing algebra `W`. -/
def act : Γ r m →* (W R A r m ≃ₐ[R] W R A r m) := twistAction

omit [DecidableEq r] in
theorem act_toAlgHom (γ : Γ r m) :
    ((act R A r m γ : W R A r m ≃ₐ[R] W R A r m) : W R A r m →ₐ[R] W R A r m) =
      twistHom (-(Multiplicative.toAdd γ) : AddAut (r → ZMod m)).toAddMonoidHom := by
  apply AlgHom.ext
  intro w
  rfl

variable {R A r m}

omit [DecidableEq r] in
/-- Points compose with changes of coefficients. -/
theorem pointOf_comp {C D : Type*} [CommRing C] [Algebra R C] [CommRing D] [Algebra R D]
    (g : W R A r m →ₐ[R] C) (h : C →ₐ[R] D) :
    pointOf R A r m (h.comp g) =
      (AddMonoidAlgebra.mapAlgHom (r → ZMod m) h).comp (pointOf R A r m g) := by
  apply AlgHom.ext
  intro x
  apply AddMonoidAlgebra.coeff_injective
  ext b
  simp [pointOf, AddMonoidAlgebra.coeff_mapAlgHom]

omit [DecidableEq r] in
/-- Acting by `γ` twists the Hopf point of a point by `γ⁻¹`. -/
theorem pointOf_comp_act {C : Type*} [CommRing C] [Algebra R C] (g : W R A r m →ₐ[R] C)
    (γ : Γ r m) :
    pointOf R A r m (g.comp (act R A r m γ : W R A r m →ₐ[R] W R A r m)) =
      (AddMonoidAlgebra.mapDomainAlgHom R C
        (-(Multiplicative.toAdd γ) : AddAut (r → ZMod m)).toAddMonoidHom).comp
        (pointOf R A r m g) := by
  rw [act_toAlgHom, pointOf_comp_twistHom]

omit [DecidableEq r] in
/-- A point of `W` is determined by its Hopf point. -/
theorem pointOf_injective {C : Type u} [CommRing C] [Algebra R C] :
    Function.Injective (pointOf R A r m (C := C)) := by
  intro g g' h
  have h1 := univ_point R A r m g
  have h2 := univ_point R A r m g'
  rw [← pointOf, h] at h1
  rw [← pointOf] at h2
  have h3 : (homEquiv R A (AddMonoidAlgebra R (r → ZMod m)) C g).1 =
      (homEquiv R A (AddMonoidAlgebra R (r → ZMod m)) C g').1 := by
    apply AlgHom.ext
    intro a
    have := congrArg (fun F => F a) (h1.trans h2.symm)
    simp only [toGroupAlgebra, AlgHom.comp_apply] at this
    exact (AddMonoidAlgebra.scalarTensorEquiv R C).injective this
  exact (homEquiv R A (AddMonoidAlgebra R (r → ZMod m)) C).injective (Subtype.ext h3)

omit [Algebra.FinitePresentation R A] in
/-- Pushing forward along a surjection of character groups preserves surjectivity of
the scalar extension. -/
theorem surjective_scalarExt_mapDomain {C : Type*} [CommRing C] [Algebra R C]
    {M N : Type*} [AddCommGroup M] [AddCommGroup N] (T : M →+ N) (hT : Function.Surjective T)
    {β : A →ₐ[R] AddMonoidAlgebra C M} (h : Function.Surjective (scalarExt β)) :
    Function.Surjective
      (scalarExt ((AddMonoidAlgebra.mapDomainAlgHom R C T).comp β)) := by
  rw [HopfPointKernel.scalarExt_comp_mapDomain, AlgHom.coe_comp]
  refine Function.Surjective.comp ?_ h
  intro y
  obtain ⟨x, hx⟩ := Finsupp.mapDomain_surjective hT y.coeff
  refine ⟨AddMonoidAlgebra.ofCoeff x, ?_⟩
  apply AddMonoidAlgebra.coeff_injective
  rw [← hx]
  rfl

omit [Algebra.FinitePresentation R A] in
/-- An isomorphism of character groups does not change the kernel of the scalar extension. -/
theorem ker_scalarExt_mapDomain_addEquiv₂ {C : Type*} [CommRing C] [Algebra R C]
    {M N : Type*} [AddCommGroup M] [AddCommGroup N] (T : M ≃+ N)
    (β : A →ₐ[R] AddMonoidAlgebra C M) :
    RingHom.ker (scalarExt ((AddMonoidAlgebra.mapDomainAlgHom R C T.toAddMonoidHom).comp β)) =
      RingHom.ker (scalarExt β) := by
  rw [HopfPointKernel.scalarExt_comp_mapDomain]
  ext x
  simp only [RingHom.mem_ker, AlgHom.comp_apply]
  constructor
  · intro h
    have hinj : Function.Injective (AddMonoidAlgebra.mapDomainAlgHom C C T.toAddMonoidHom) := by
      intro a b hab
      apply AddMonoidAlgebra.coeff_injective
      exact Finsupp.mapDomain_injective T.injective (congrArg AddMonoidAlgebra.coeff hab)
    exact hinj (by rw [h, map_zero])
  · intro h
    rw [h, map_zero]

omit [Algebra.FinitePresentation R A] in
/-- Changing coefficients does not enlarge supports. -/
theorem support_mapAlgHom_subset {C D : Type*} [CommRing C] [Algebra R C] [CommRing D]
    [Algebra R D] {M : Type*} [AddCommGroup M] (h : C →ₐ[R] D) (x : AddMonoidAlgebra C M) :
    ((AddMonoidAlgebra.mapAlgHom M h x).coeff.support : Set M) ⊆ x.coeff.support := by
  intro b hb
  simp only [Finset.mem_coe, Finsupp.mem_support_iff, AddMonoidAlgebra.coeff_mapAlgHom] at hb ⊢
  intro h0
  rw [h0, map_zero] at hb
  exact hb rfl


section TensorForm

variable {C : Type u} [CommRing C] [Algebra R C] {M : Type u} [AddCommGroup M]

omit [Algebra.FinitePresentation R A] in
/-- The scalar extension of the group-algebra form is the linear extension of the tensor
form, followed by the identification `C ⊗[R] R[M] ≅ C[M]`. -/
theorem scalarExt_toGroupAlgebra (f : A →ₐ[R] C ⊗[R] AddMonoidAlgebra R M) :
    scalarExt (toGroupAlgebra f) =
      (AddMonoidAlgebra.scalarTensorEquiv R C (M := M)).toAlgHom.comp
        (AlgHom.liftEquiv R C A _ f) := by
  apply Algebra.TensorProduct.ext_ring
  apply AlgHom.ext
  intro a
  simp [scalarExt_tmul]

omit [Algebra.FinitePresentation R A] in
theorem ker_liftEquiv (f : A →ₐ[R] C ⊗[R] AddMonoidAlgebra R M) :
    RingHom.ker (AlgHom.liftEquiv R C A _ f) = RingHom.ker (scalarExt (toGroupAlgebra f)) := by
  rw [scalarExt_toGroupAlgebra]
  ext x
  simp only [RingHom.mem_ker, AlgHom.coe_comp, Function.comp_apply, AlgEquiv.coe_toAlgHom]
  exact (map_eq_zero_iff _ (AddMonoidAlgebra.scalarTensorEquiv R C (M := M)).injective).symm

omit [Algebra.FinitePresentation R A] in
theorem surjective_liftEquiv_iff (f : A →ₐ[R] C ⊗[R] AddMonoidAlgebra R M) :
    Function.Surjective (AlgHom.liftEquiv R C A _ f) ↔
      Function.Surjective (scalarExt (toGroupAlgebra f)) := by
  rw [scalarExt_toGroupAlgebra, AlgHom.coe_comp]
  constructor
  · intro h
    exact (AddMonoidAlgebra.scalarTensorEquiv R C (M := M)).surjective.comp h
  · intro h y
    obtain ⟨x, hx⟩ := h (AddMonoidAlgebra.scalarTensorEquiv R C (M := M) y)
    exact ⟨x, (AddMonoidAlgebra.scalarTensorEquiv R C (M := M)).injective hx⟩

/-- The tensor form of a point `A → C[M]`. -/
def ofGroupAlgebra (α : A →ₐ[R] AddMonoidAlgebra C M) : A →ₐ[R] C ⊗[R] AddMonoidAlgebra R M :=
  ((AddMonoidAlgebra.scalarTensorEquiv R C (M := M)).symm.toAlgHom.restrictScalars R).comp α

omit [Algebra.FinitePresentation R A] in
@[simp] theorem toGroupAlgebra_ofGroupAlgebra (α : A →ₐ[R] AddMonoidAlgebra C M) :
    toGroupAlgebra (ofGroupAlgebra α) = α := by
  apply AlgHom.ext
  intro a
  simp [ofGroupAlgebra]

omit [Algebra.FinitePresentation R A] in
theorem isHopfPoint_ofGroupAlgebra {α : A →ₐ[R] AddMonoidAlgebra C M} (hα : IsHopfPoint α) :
    FiniteBialgebraHom.IsHopfPoint R (ofGroupAlgebra α) := by
  rw [isHopfPoint_iff, toGroupAlgebra_ofGroupAlgebra]
  exact hα

end TensorForm

variable (R A r m) {σ' : Type u} (gen : σ' → A) (n : ℕ)

/-- The ring-level data of a chart: an element `f` of `W` over whose principal open
the universal point of `μ_m^r` extends to a closed-immersion Hopf point `α` of the torus
with weights of the generators in the box of size `n`, and an invariant element `N`
whose principal open is covered by the translates of `D(f)`. -/
structure Datum where
  bound : rigidityBound r n ≤ m
  adjoin_gen : Algebra.adjoin R (Set.range gen) = ⊤
  f : W R A r m
  N : W R A r m
  α : A →ₐ[R] AddMonoidAlgebra (Localization.Away f) (r → ℤ)
  isHopfPoint : IsHopfPoint α
  support : ∀ i, ↑(α (gen i)).coeff.support ⊆ (box r n : Set (r → ℤ))
  red_comp : (AddMonoidAlgebra.mapDomainAlgHom R _ (red r m)).comp α =
    pointOf R A r m (IsScalarTower.toAlgHom R (W R A r m) (Localization.Away f))
  surjective : Function.Surjective (scalarExt α)
  invariant : ∀ γ, act R A r m γ N = N
  cover : ∀ P : Ideal (W R A r m), P.IsPrime → N ∉ P → ∃ γ, act R A r m γ f ∉ P

namespace Datum

variable {R A r m gen n} (d : Datum R A r m gen n)

/-- The coordinate ring of the invariant principal open. -/
abbrev B : Type u := Localization.Away d.N

/-- The action of `Γ` on `B`. -/
def actB : Γ r m →* (d.B ≃+* d.B) :=
  awayAction (act R A r m) d.invariant

theorem actB_algebraMap (γ : Γ r m) (w : W R A r m) :
    d.actB γ (algebraMap (W R A r m) d.B w) =
      algebraMap (W R A r m) d.B (act R A r m γ w) :=
  awayAction_algebraMap _ d.invariant γ w

theorem actB_algebraMap_R (γ : Γ r m) (x : R) :
    d.actB γ (algebraMap R d.B x) = algebraMap R d.B x := by
  rw [IsScalarTower.algebraMap_apply R (W R A r m) d.B, actB_algebraMap, AlgEquiv.commutes]

/-- The action of `Γ` on `B` by `R`-algebra automorphisms. -/
def actBAlg (γ : Γ r m) : d.B ≃ₐ[R] d.B :=
  { d.actB γ with commutes' := d.actB_algebraMap_R γ }

/-- Extension of a point through `D(f)`. -/
theorem exists_lift {C : Type*} [CommRing C] [Algebra R C] (g : W R A r m →ₐ[R] C)
    (hg : IsUnit (g d.f)) :
    ∃ g' : Localization.Away d.f →ₐ[R] C,
      g'.comp (IsScalarTower.toAlgHom R (W R A r m) (Localization.Away d.f)) = g := by
  have hunit : ∀ y : Submonoid.powers d.f, IsUnit (g y) := by
    rintro ⟨y, k, rfl⟩
    simpa using hg.pow k
  refine ⟨IsLocalization.liftAlgHom (M := Submonoid.powers d.f) hunit, ?_⟩
  apply AlgHom.ext
  intro w
  simp [IsLocalization.lift_eq]

/-- At a point through `D(f)`, the Hopf point of `μ_m^r` is a closed immersion. -/
theorem surjective_pointOf_of_isUnit {C : Type*} [CommRing C] [Algebra R C]
    (g : W R A r m →ₐ[R] C) (hg : IsUnit (g d.f)) :
    Function.Surjective (scalarExt (pointOf R A r m g)) := by
  obtain ⟨g', rfl⟩ := d.exists_lift g hg
  rw [pointOf_comp, ← d.red_comp, ← AlgHom.comp_assoc,
    HopfPointWindowExtension.mapAlgHom_comp_mapDomain, AlgHom.comp_assoc]
  apply surjective_scalarExt_mapDomain _ (red_surjective r m)
  exact surjective_scalarExt_mapAlgHom g' d.surjective

/-- At every field point of `B`, the Hopf point of `μ_m^r` is a closed immersion. -/
theorem surjective_pointOf_of_field {K : Type*} [Field K] [Algebra R K]
    (g : W R A r m →ₐ[R] K) (hN : g d.N ≠ 0) :
    Function.Surjective (scalarExt (pointOf R A r m g)) := by
  have hP : (RingHom.ker g.toRingHom).IsPrime := RingHom.ker_isPrime _
  obtain ⟨γ, hγ⟩ := d.cover _ hP (by simpa [RingHom.mem_ker] using hN)
  have hunit : IsUnit ((g.comp (act R A r m γ : W R A r m →ₐ[R] W R A r m)) d.f) := by
    rw [isUnit_iff_ne_zero]
    simpa [RingHom.mem_ker] using hγ
  have h1 := d.surjective_pointOf_of_isUnit _ hunit
  rw [pointOf_comp_act] at h1
  have h2 := surjective_scalarExt_mapDomain
    ((Multiplicative.toAdd γ : AddAut (r → ZMod m)) : (r → ZMod m) →+ (r → ZMod m))
    (Multiplicative.toAdd γ).surjective h1
  rw [← AlgHom.comp_assoc, ← AddMonoidAlgebra.mapDomainAlgHom_comp] at h2
  convert h2 using 3
  have : ((Multiplicative.toAdd γ : AddAut (r → ZMod m)) : (r → ZMod m) →+ (r → ZMod m)).comp
      (-(Multiplicative.toAdd γ) : AddAut (r → ZMod m)).toAddMonoidHom = AddMonoidHom.id _ := by
    ext x
    simp
  rw [this, AddMonoidAlgebra.mapDomainAlgHom_id, AlgHom.id_comp]

/-- Freeness of the action on `B` at field-valued points. -/
theorem actB_free (K : Type u) [Field K] (φ : d.B →+* K) (γ δ : Γ r m)
    (h : φ.comp (d.actB γ).toRingHom = φ.comp (d.actB δ).toRingHom) : γ = δ := by
  let ψ : W R A r m →+* K := φ.comp (algebraMap (W R A r m) d.B)
  let : Algebra R K := (ψ.comp (algebraMap R (W R A r m))).toAlgebra
  let g : W R A r m →ₐ[R] K := { ψ with commutes' := fun _ => rfl }
  have hN : g d.N ≠ 0 := by
    change φ (algebraMap (W R A r m) d.B d.N) ≠ 0
    exact ((IsLocalization.Away.algebraMap_isUnit d.N).map φ).ne_zero
  have hsurj := d.surjective_pointOf_of_field g hN
  have hW : g.comp (act R A r m γ : W R A r m →ₐ[R] W R A r m) =
      g.comp (act R A r m δ : W R A r m →ₐ[R] W R A r m) := by
    apply AlgHom.ext
    intro w
    have := congrArg (fun F => F (algebraMap (W R A r m) d.B w)) h
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      actB_algebraMap] at this
    exact this
  have hpt := congrArg (pointOf R A r m) hW
  rw [act_toAlgHom, act_toAlgHom] at hpt
  have := TorusChartAlgebra.twist_injective_of_surjective R A r m g hsurj _ _ hpt
  have h' : Multiplicative.toAdd γ = Multiplicative.toAdd δ := neg_injective this
  exact h'


/-- The extension pushed to an algebra under `D(f)`. -/
def pushα {C : Type*} [CommRing C] [Algebra R C] (u : Localization.Away d.f →ₐ[R] C) :
    A →ₐ[R] AddMonoidAlgebra C (r → ℤ) :=
  (AddMonoidAlgebra.mapAlgHom (r → ℤ) u).comp d.α

theorem isHopfPoint_pushα {C : Type*} [CommRing C] [Algebra R C]
    (u : Localization.Away d.f →ₐ[R] C) : IsHopfPoint (d.pushα u) :=
  HopfPointWindowExtension.IsHopfPoint.mapAlgHom u d.isHopfPoint

theorem support_pushα {C : Type*} [CommRing C] [Algebra R C]
    (u : Localization.Away d.f →ₐ[R] C) (i : σ') :
    ↑(d.pushα u (gen i)).coeff.support ⊆ (box r n : Set (r → ℤ)) :=
  (support_mapAlgHom_subset u _).trans (d.support i)

theorem surjective_pushα {C : Type*} [CommRing C] [Algebra R C]
    (u : Localization.Away d.f →ₐ[R] C) : Function.Surjective (scalarExt (d.pushα u)) :=
  surjective_scalarExt_mapAlgHom u d.surjective

theorem red_comp_pushα {C : Type*} [CommRing C] [Algebra R C]
    (u : Localization.Away d.f →ₐ[R] C) :
    (AddMonoidAlgebra.mapDomainAlgHom R C (red r m)).comp (d.pushα u) =
      pointOf R A r m (u.comp (IsScalarTower.toAlgHom R (W R A r m) (Localization.Away d.f))) := by
  rw [pushα, ← AlgHom.comp_assoc, ← HopfPointWindowExtension.mapAlgHom_comp_mapDomain,
    AlgHom.comp_assoc, d.red_comp, pointOf_comp]

theorem mapAlgHom_comp_pushα {C D : Type*} [CommRing C] [Algebra R C] [CommRing D]
    [Algebra R D] (u : Localization.Away d.f →ₐ[R] C) (h : C →ₐ[R] D) :
    (AddMonoidAlgebra.mapAlgHom (r → ℤ) h).comp (d.pushα u) = d.pushα (h.comp u) := by
  apply AlgHom.ext
  intro x
  apply AddMonoidAlgebra.coeff_injective
  ext b
  simp [pushα, AddMonoidAlgebra.coeff_mapAlgHom]

/-- Rigidity on overlaps: two pushed extensions whose points of `W` differ by the action of
`γ` have the same kernel after scalar extension, hence the same range. -/
theorem ker_pushα_eq {C : Type*} [CommRing C] [Algebra R C] (u₁ u₂ : Localization.Away d.f →ₐ[R] C)
    (γ : Γ r m)
    (h : u₁.comp (IsScalarTower.toAlgHom R (W R A r m) (Localization.Away d.f)) =
      (u₂.comp (IsScalarTower.toAlgHom R (W R A r m) (Localization.Away d.f))).comp
        (act R A r m γ : W R A r m →ₐ[R] W R A r m)) :
    RingHom.ker (scalarExt (d.pushα u₁)) = RingHom.ker (scalarExt (d.pushα u₂)) := by
  rcases subsingleton_or_nontrivial C with hC | hC
  · have : Subsingleton (C ⊗[R] A) := by
      refine ⟨fun x y => ?_⟩
      have h1 : (1 : C ⊗[R] A) = 0 := by
        rw [Algebra.TensorProduct.one_def, Subsingleton.elim (1 : C) 0, TensorProduct.zero_tmul]
      rw [← one_mul x, ← one_mul y, h1, zero_mul, zero_mul]
    exact Subsingleton.elim _ _
  · have hg₁ := closure_support_eq_top d.adjoin_gen (adjoin_range_eq_top (d.surjective_pushα u₁))
    have hg₂ := closure_support_eq_top d.adjoin_gen (adjoin_range_eq_top (d.surjective_pushα u₂))
    apply HopfPointKernel.ker_scalarExt_eq_of_red_eq d.bound d.adjoin_gen (d.support_pushα u₂)
      (d.support_pushα u₁) hg₂ hg₁ (-(Multiplicative.toAdd γ) : AddAut (r → ZMod m))
    rw [d.red_comp_pushα, d.red_comp_pushα, h, pointOf_comp_act]

/-- Injectivity on overlaps: two pushed extensions with the same kernel come, locally at
every maximal ideal, from points of `W` differing by the action of `Γ`. -/
theorem exists_act_of_ker_eq {C : Type u} [CommRing C] [Algebra R C]
    (u₁ u₂ : Localization.Away d.f →ₐ[R] C)
    (h : RingHom.ker (scalarExt (d.pushα u₁)) = RingHom.ker (scalarExt (d.pushα u₂)))
    (P : Ideal C) [P.IsMaximal] :
    ∃ γ : Γ r m,
      ((IsScalarTower.toAlgHom R C (Localization.AtPrime P)).comp u₂).comp
          (IsScalarTower.toAlgHom R (W R A r m) (Localization.Away d.f)) =
        (((IsScalarTower.toAlgHom R C (Localization.AtPrime P)).comp u₁).comp
          (IsScalarTower.toAlgHom R (W R A r m) (Localization.Away d.f))).comp
          (act R A r m γ : W R A r m →ₐ[R] W R A r m) := by
  let loc := IsScalarTower.toAlgHom R C (Localization.AtPrime P)
  obtain ⟨T, hT⟩ := HopfPointConnected.exists_addEquiv_localization (d.isHopfPoint_pushα u₁)
    (d.isHopfPoint_pushα u₂) (d.surjective_pushα u₁) (d.surjective_pushα u₂) h P
  rw [d.mapAlgHom_comp_pushα, d.mapAlgHom_comp_pushα] at hT
  obtain ⟨Tb, hTb⟩ := exists_red_equiv m T
  refine ⟨Multiplicative.ofAdd (-Tb), ?_⟩
  apply pointOf_injective
  rw [pointOf_comp_act, ← d.red_comp_pushα, ← d.red_comp_pushα, ← hT, ← AlgHom.comp_assoc,
    ← AlgHom.comp_assoc, ← AddMonoidAlgebra.mapDomainAlgHom_comp,
    ← AddMonoidAlgebra.mapDomainAlgHom_comp]
  congr 2
  ext x
  simp [hTb]

end Datum

end Langlands.Algebra.TorusChartRing
