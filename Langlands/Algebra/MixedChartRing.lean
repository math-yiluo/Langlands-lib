import Langlands.Algebra.MixedChartAlgebra
import Langlands.Algebra.MixedHopfPointRigidity
import Langlands.Algebra.TorusChartRing
import Langlands.Algebra.HopfPointClosedLocus
import Langlands.Algebra.HopfPointConnected

/-! # Ring-level data of a chart for subgroups of multiplicative type -/

noncomputable section

universe u

open TensorProduct

namespace Langlands.Algebra.MixedChartRing

open HopfPointExtension HopfPointBridge HopfPointTwist FiniteBialgebraHom MixedChartAlgebra
  HopfPointClosedLocus LatticeConfiguration MixedLatticeConfiguration InvariantPrincipalOpen
  MixedHopfPointRigidity

section Generic

variable (R : Type u) [CommRing R] (A : Type u) [CommRing A] [HopfAlgebra R A]
  [Algebra.FinitePresentation R A] (L : Type u) [AddCommGroup L] [Fintype L]

/-- The twisting group `Aut(L)`, written multiplicatively. -/
abbrev Γ : Type u := Multiplicative (AddAut L)

omit [AddCommGroup L] in
/-- The twisting group is finite. -/
instance {L : Type u} [AddCommGroup L] [Finite L] : Finite (Γ L) := by
  change Finite (Multiplicative (L ≃+ L))
  have : Finite (L ≃+ L) :=
    Finite.of_injective (fun e : L ≃+ L => (e : L → L))
      (fun a b h => AddEquiv.ext (congrFun h))
  infer_instance

/-- The twisting action of `Γ` on the representing algebra `W`. -/
def act : Γ L →* (W R A L ≃ₐ[R] W R A L) := twistAction

theorem act_toAlgHom (γ : Γ L) :
    ((act R A L γ : W R A L ≃ₐ[R] W R A L) : W R A L →ₐ[R] W R A L) =
      twistHom (-(Multiplicative.toAdd γ) : AddAut L).toAddMonoidHom := by
  apply AlgHom.ext
  intro w
  rfl

variable {R A L}

/-- Points compose with changes of coefficients. -/
theorem pointOf_comp {C D : Type*} [CommRing C] [Algebra R C] [CommRing D] [Algebra R D]
    (g : W R A L →ₐ[R] C) (h : C →ₐ[R] D) :
    pointOf R A L (h.comp g) = (AddMonoidAlgebra.mapAlgHom L h).comp (pointOf R A L g) := by
  apply AlgHom.ext
  intro x
  apply AddMonoidAlgebra.coeff_injective
  ext b
  simp [pointOf, AddMonoidAlgebra.coeff_mapAlgHom]

/-- Acting by `γ` twists the Hopf point of a point by `γ⁻¹`. -/
theorem pointOf_comp_act {C : Type*} [CommRing C] [Algebra R C] (g : W R A L →ₐ[R] C)
    (γ : Γ L) :
    pointOf R A L (g.comp (act R A L γ : W R A L →ₐ[R] W R A L)) =
      (AddMonoidAlgebra.mapDomainAlgHom R C
        (-(Multiplicative.toAdd γ) : AddAut L).toAddMonoidHom).comp (pointOf R A L g) := by
  rw [act_toAlgHom, pointOf_comp_twistHom]

/-- A point of `W` is determined by its Hopf point. -/
theorem pointOf_injective {C : Type u} [CommRing C] [Algebra R C] :
    Function.Injective (pointOf R A L (C := C)) := by
  intro g g' h
  have h1 := univ_point R A L g
  have h2 := univ_point R A L g'
  rw [← pointOf, h] at h1
  rw [← pointOf] at h2
  have h3 : (homEquiv R A (AddMonoidAlgebra R L) C g).1 =
      (homEquiv R A (AddMonoidAlgebra R L) C g').1 := by
    apply AlgHom.ext
    intro a
    have := congrArg (fun F => F a) (h1.trans h2.symm)
    simp only [toGroupAlgebra, AlgHom.comp_apply] at this
    exact (AddMonoidAlgebra.scalarTensorEquiv R C).injective this
  exact (homEquiv R A (AddMonoidAlgebra R L) C).injective (Subtype.ext h3)

end Generic

variable (R : Type u) [CommRing R] (A : Type u) [CommRing A] [HopfAlgebra R A]
  [Algebra.FinitePresentation R A] (r : Type u) [Fintype r] [DecidableEq r]
  (F : Type u) [AddCommGroup F] [Fintype F] (m : ℕ) [NeZero m]
  {σ' : Type u} (gen : σ' → A) (n : ℕ)

/-- The ring-level data of a chart: an element `f` of `W` over whose principal open
the universal point of `D((ℤ/m)^r × F)` extends to a closed-immersion Hopf point `α` of
`D(ℤ^r × F)` with weights of the generators in the box of size `n`, and an invariant
element `N` whose principal open is covered by the translates of `D(f)`. -/
structure Datum where
  bound : rigidityBound r F n ≤ m
  torsion : ∀ x : F, m • x = 0
  adjoin_gen : Algebra.adjoin R (Set.range gen) = ⊤
  f : W R A ((r → ZMod m) × F)
  N : W R A ((r → ZMod m) × F)
  α : A →ₐ[R] AddMonoidAlgebra (Localization.Away f) ((r → ℤ) × F)
  isHopfPoint : IsHopfPoint α
  support : ∀ i, ↑(α (gen i)).coeff.support ⊆ (mbox r F n : Set ((r → ℤ) × F))
  red_comp : (AddMonoidAlgebra.mapDomainAlgHom R _ (mred r F m)).comp α =
    pointOf R A ((r → ZMod m) × F)
      (IsScalarTower.toAlgHom R (W R A ((r → ZMod m) × F)) (Localization.Away f))
  surjective : Function.Surjective (scalarExt α)
  invariant : ∀ γ, act R A ((r → ZMod m) × F) γ N = N
  cover : ∀ P : Ideal (W R A ((r → ZMod m) × F)), P.IsPrime → N ∉ P →
    ∃ γ, act R A ((r → ZMod m) × F) γ f ∉ P

namespace Datum

variable {R A r F m gen n} (d : Datum R A r F m gen n)

local notation "Lb" => (r → ZMod m) × F
local notation "Λ" => (r → ℤ) × F

/-- The coordinate ring of the invariant principal open. -/
abbrev B : Type u := Localization.Away d.N

/-- The action of `Γ` on `B`. -/
def actB : Γ Lb →* (d.B ≃+* d.B) :=
  awayAction (act R A Lb) d.invariant

theorem actB_algebraMap (γ : Γ Lb) (w : W R A Lb) :
    d.actB γ (algebraMap (W R A Lb) d.B w) = algebraMap (W R A Lb) d.B (act R A Lb γ w) :=
  awayAction_algebraMap _ d.invariant γ w

theorem actB_algebraMap_R (γ : Γ Lb) (x : R) :
    d.actB γ (algebraMap R d.B x) = algebraMap R d.B x := by
  rw [IsScalarTower.algebraMap_apply R (W R A Lb) d.B, actB_algebraMap, AlgEquiv.commutes]

/-- The action of `Γ` on `B` by `R`-algebra automorphisms. -/
def actBAlg (γ : Γ Lb) : d.B ≃ₐ[R] d.B :=
  { d.actB γ with commutes' := d.actB_algebraMap_R γ }

/-- Extension of a point through `D(f)`. -/
theorem exists_lift {C : Type*} [CommRing C] [Algebra R C] (g : W R A Lb →ₐ[R] C)
    (hg : IsUnit (g d.f)) :
    ∃ g' : Localization.Away d.f →ₐ[R] C,
      g'.comp (IsScalarTower.toAlgHom R (W R A Lb) (Localization.Away d.f)) = g := by
  have hunit : ∀ y : Submonoid.powers d.f, IsUnit (g y) := by
    rintro ⟨y, k, rfl⟩
    simpa using hg.pow k
  refine ⟨IsLocalization.liftAlgHom (M := Submonoid.powers d.f) hunit, ?_⟩
  apply AlgHom.ext
  intro w
  simp [IsLocalization.lift_eq]

/-- At a point through `D(f)`, the Hopf point of `D((ℤ/m)^r × F)` is a closed immersion. -/
theorem surjective_pointOf_of_isUnit {C : Type*} [CommRing C] [Algebra R C]
    (g : W R A Lb →ₐ[R] C) (hg : IsUnit (g d.f)) :
    Function.Surjective (scalarExt (pointOf R A Lb g)) := by
  obtain ⟨g', rfl⟩ := d.exists_lift g hg
  rw [pointOf_comp, ← d.red_comp, ← AlgHom.comp_assoc,
    HopfPointWindowExtension.mapAlgHom_comp_mapDomain, AlgHom.comp_assoc]
  apply TorusChartRing.surjective_scalarExt_mapDomain _ (mred_surjective r F m)
  exact surjective_scalarExt_mapAlgHom g' d.surjective

/-- At every field point of `B`, the Hopf point of `D((ℤ/m)^r × F)` is a closed
immersion. -/
theorem surjective_pointOf_of_field {K : Type*} [Field K] [Algebra R K]
    (g : W R A Lb →ₐ[R] K) (hN : g d.N ≠ 0) :
    Function.Surjective (scalarExt (pointOf R A Lb g)) := by
  have hP : (RingHom.ker g.toRingHom).IsPrime := RingHom.ker_isPrime _
  obtain ⟨γ, hγ⟩ := d.cover _ hP (by simpa [RingHom.mem_ker] using hN)
  have hunit : IsUnit ((g.comp (act R A Lb γ : W R A Lb →ₐ[R] W R A Lb)) d.f) := by
    rw [isUnit_iff_ne_zero]
    simpa [RingHom.mem_ker] using hγ
  have h1 := d.surjective_pointOf_of_isUnit _ hunit
  rw [pointOf_comp_act] at h1
  have h2 := TorusChartRing.surjective_scalarExt_mapDomain
    ((Multiplicative.toAdd γ : AddAut Lb) : Lb →+ Lb)
    (Multiplicative.toAdd γ).surjective h1
  rw [← AlgHom.comp_assoc, ← AddMonoidAlgebra.mapDomainAlgHom_comp] at h2
  convert h2 using 3
  have : ((Multiplicative.toAdd γ : AddAut Lb) : Lb →+ Lb).comp
      (-(Multiplicative.toAdd γ) : AddAut Lb).toAddMonoidHom = AddMonoidHom.id _ :=
    AddMonoidHom.ext fun x => by simp
  rw [this, AddMonoidAlgebra.mapDomainAlgHom_id, AlgHom.id_comp]

/-- Freeness of the action on `B` at field-valued points. -/
theorem actB_free (K : Type u) [Field K] (φ : d.B →+* K) (γ δ : Γ Lb)
    (h : φ.comp (d.actB γ).toRingHom = φ.comp (d.actB δ).toRingHom) : γ = δ := by
  let ψ : W R A Lb →+* K := φ.comp (algebraMap (W R A Lb) d.B)
  let : Algebra R K := (ψ.comp (algebraMap R (W R A Lb))).toAlgebra
  let g : W R A Lb →ₐ[R] K := { ψ with commutes' := fun _ => rfl }
  have hN : g d.N ≠ 0 := by
    change φ (algebraMap (W R A Lb) d.B d.N) ≠ 0
    exact ((IsLocalization.Away.algebraMap_isUnit d.N).map φ).ne_zero
  have hsurj := d.surjective_pointOf_of_field g hN
  have hW : g.comp (act R A Lb γ : W R A Lb →ₐ[R] W R A Lb) =
      g.comp (act R A Lb δ : W R A Lb →ₐ[R] W R A Lb) := by
    apply AlgHom.ext
    intro w
    have := congrArg (fun F => F (algebraMap (W R A Lb) d.B w)) h
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      actB_algebraMap] at this
    exact this
  have hpt := congrArg (pointOf R A Lb) hW
  rw [act_toAlgHom, act_toAlgHom] at hpt
  have := MixedChartAlgebra.twist_injective_of_surjective R A Lb g hsurj _ _ hpt
  have h' : Multiplicative.toAdd γ = Multiplicative.toAdd δ := neg_injective this
  exact h'

/-- The extension pushed to an algebra under `D(f)`. -/
def pushα {C : Type*} [CommRing C] [Algebra R C] (u : Localization.Away d.f →ₐ[R] C) :
    A →ₐ[R] AddMonoidAlgebra C Λ :=
  (AddMonoidAlgebra.mapAlgHom Λ u).comp d.α

theorem isHopfPoint_pushα {C : Type*} [CommRing C] [Algebra R C]
    (u : Localization.Away d.f →ₐ[R] C) : IsHopfPoint (d.pushα u) :=
  HopfPointWindowExtension.IsHopfPoint.mapAlgHom u d.isHopfPoint

theorem support_pushα {C : Type*} [CommRing C] [Algebra R C]
    (u : Localization.Away d.f →ₐ[R] C) (i : σ') :
    ↑(d.pushα u (gen i)).coeff.support ⊆ (mbox r F n : Set Λ) :=
  (TorusChartRing.support_mapAlgHom_subset u _).trans (d.support i)

theorem surjective_pushα {C : Type*} [CommRing C] [Algebra R C]
    (u : Localization.Away d.f →ₐ[R] C) : Function.Surjective (scalarExt (d.pushα u)) :=
  surjective_scalarExt_mapAlgHom u d.surjective

theorem red_comp_pushα {C : Type*} [CommRing C] [Algebra R C]
    (u : Localization.Away d.f →ₐ[R] C) :
    (AddMonoidAlgebra.mapDomainAlgHom R C (mred r F m)).comp (d.pushα u) =
      pointOf R A Lb (u.comp (IsScalarTower.toAlgHom R (W R A Lb) (Localization.Away d.f))) := by
  rw [pushα, ← AlgHom.comp_assoc, ← HopfPointWindowExtension.mapAlgHom_comp_mapDomain,
    AlgHom.comp_assoc, d.red_comp, pointOf_comp]

theorem mapAlgHom_comp_pushα {C D : Type*} [CommRing C] [Algebra R C] [CommRing D]
    [Algebra R D] (u : Localization.Away d.f →ₐ[R] C) (h : C →ₐ[R] D) :
    (AddMonoidAlgebra.mapAlgHom Λ h).comp (d.pushα u) = d.pushα (h.comp u) := by
  apply AlgHom.ext
  intro x
  apply AddMonoidAlgebra.coeff_injective
  ext b
  simp [pushα, AddMonoidAlgebra.coeff_mapAlgHom]

/-- Rigidity on overlaps: two pushed extensions whose points of `W` differ by the action of
`γ` have the same kernel after scalar extension, hence the same range. -/
theorem ker_pushα_eq {C : Type*} [CommRing C] [Algebra R C]
    (u₁ u₂ : Localization.Away d.f →ₐ[R] C) (γ : Γ Lb)
    (h : u₁.comp (IsScalarTower.toAlgHom R (W R A Lb) (Localization.Away d.f)) =
      (u₂.comp (IsScalarTower.toAlgHom R (W R A Lb) (Localization.Away d.f))).comp
        (act R A Lb γ : W R A Lb →ₐ[R] W R A Lb)) :
    RingHom.ker (scalarExt (d.pushα u₁)) = RingHom.ker (scalarExt (d.pushα u₂)) := by
  rcases subsingleton_or_nontrivial C with hC | hC
  · have : Subsingleton (C ⊗[R] A) := by
      refine ⟨fun x y => ?_⟩
      have h1 : (1 : C ⊗[R] A) = 0 := by
        rw [Algebra.TensorProduct.one_def, Subsingleton.elim (1 : C) 0, TensorProduct.zero_tmul]
      rw [← one_mul x, ← one_mul y, h1, zero_mul, zero_mul]
    exact Subsingleton.elim _ _
  · have hg₁ := closure_support_eq_top d.adjoin_gen
      (adjoin_range_eq_top (d.surjective_pushα u₁))
    have hg₂ := closure_support_eq_top d.adjoin_gen
      (adjoin_range_eq_top (d.surjective_pushα u₂))
    apply ker_scalarExt_eq_of_mred_eq d.bound d.adjoin_gen (d.support_pushα u₂)
      (d.support_pushα u₁) hg₂ hg₁ (-(Multiplicative.toAdd γ) : AddAut Lb)
    rw [d.red_comp_pushα, d.red_comp_pushα, h, pointOf_comp_act]

/-- Injectivity on overlaps: two pushed extensions with the same kernel come, locally at
every maximal ideal, from points of `W` differing by the action of `Γ`. -/
theorem exists_act_of_ker_eq {C : Type u} [CommRing C] [Algebra R C]
    (u₁ u₂ : Localization.Away d.f →ₐ[R] C)
    (h : RingHom.ker (scalarExt (d.pushα u₁)) = RingHom.ker (scalarExt (d.pushα u₂)))
    (P : Ideal C) [P.IsMaximal] :
    ∃ γ : Γ Lb,
      ((IsScalarTower.toAlgHom R C (Localization.AtPrime P)).comp u₂).comp
          (IsScalarTower.toAlgHom R (W R A Lb) (Localization.Away d.f)) =
        (((IsScalarTower.toAlgHom R C (Localization.AtPrime P)).comp u₁).comp
          (IsScalarTower.toAlgHom R (W R A Lb) (Localization.Away d.f))).comp
          (act R A Lb γ : W R A Lb →ₐ[R] W R A Lb) := by
  obtain ⟨T, hT⟩ := HopfPointConnected.exists_addEquiv_localization (d.isHopfPoint_pushα u₁)
    (d.isHopfPoint_pushα u₂) (d.surjective_pushα u₁) (d.surjective_pushα u₂) h P
  rw [d.mapAlgHom_comp_pushα, d.mapAlgHom_comp_pushα] at hT
  obtain ⟨Tb, hTb⟩ := exists_mred_equiv d.torsion T
  refine ⟨Multiplicative.ofAdd (-Tb), ?_⟩
  apply pointOf_injective
  rw [pointOf_comp_act, ← d.red_comp_pushα, ← d.red_comp_pushα, ← hT, ← AlgHom.comp_assoc,
    ← AlgHom.comp_assoc, ← AddMonoidAlgebra.mapDomainAlgHom_comp,
    ← AddMonoidAlgebra.mapDomainAlgHom_comp]
  congr 2
  refine AddMonoidHom.ext fun x => ?_
  simp [-mred_apply, hTb]

end Datum

end Langlands.Algebra.MixedChartRing
