import Langlands.GaloisCohomology.Global.EulerCharacteristic.Internal.KummerCount
import Langlands.GaloisCohomology.Local.EulerCharacteristic.Coprime

/-!
# Dimensions of cohomology through an open normal subgroup of index prime to `ℓ`

Let `G` be a profinite group, `P` an open normal subgroup with quotient identified with a finite
group `Γ` of order prime to the prime `ℓ` (`e : G ⧸ P ≃* Γ`), `T` a smooth `G`-module killed by `ℓ`
of dimension one over `𝔽_ℓ` on which `P` acts trivially, and `M` a finite smooth `G`-module killed by
`ℓ` on which `P` acts trivially. Then `N = Hom(T, M)` is a representation of `Γ` over `𝔽_ℓ`
(`twistRep`) and `X ↦ dim (X ⊗ N)^Γ` is an additive function `twistFun` on finite
`𝔽_ℓ[Γ]`-modules, and
`dim Hⁱ(G, M) = twistFun(Hⁱ(P, T))`
where `Γ` acts on `Hⁱ(P, T)` by conjugation (`finrank_cohomology_eq_twistFun`). This is the
library's coprime twist `finrank_cohomology_eq_finrank_invariants` written with an additive function
on `𝔽_ℓ[Γ]`-modules; it is the first step of Tate's computation of the global Euler characteristic.
-/

namespace Langlands.GaloisCohomology

open CategoryTheory Langlands.ProfiniteCohomology Langlands.GaloisCohomology.Local

universe u

noncomputable section

/-- A group killed by `ℓ` is its own `ℓ`-torsion. -/
def torsNEquivOfNsmul (ℓ : ℕ) {A : Type*} [AddCommGroup A] (h : ∀ a : A, ℓ • a = 0) :
    TorsN A ℓ ≃+ A where
  toFun x := x.1
  invFun a := ⟨a, (mem_ker_lsmul_iff ℓ a).2 (h a)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

@[simp]
theorem torsNEquivOfNsmul_apply (ℓ : ℕ) {A : Type*} [AddCommGroup A] (h : ∀ a : A, ℓ • a = 0)
    (x : TorsN A ℓ) : torsNEquivOfNsmul ℓ h x = x.1 :=
  rfl

section Twist

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  (P : OpenSubgroup G) [(P : Subgroup G).Normal] [CompactSpace (P : Subgroup G)]
  {Γ : Type u} [Group Γ] [Finite Γ] (e : G ⧸ (P : Subgroup G) ≃* Γ) (ℓ : ℕ) [Fact ℓ.Prime]
  (T M : Rep.{u} (ULift.{u} ℤ) G) [IsSmoothRep T] [IsSmoothRep M]
  (hTℓ : ∀ t : T, ℓ • t = 0) (hMℓ : ∀ m : M, ℓ • m = 0)
  (hT : ∀ (g : (P : Subgroup G)) (t : T), T.ρ g t = t)
  (hM : ∀ (g : (P : Subgroup G)) (m : M), M.ρ g m = m)

/-- `N = Hom(T, M)` as a representation of `Γ ≅ G/P` over `ULift (ZMod ℓ)`. -/
def twistRep : Representation (ULift.{u} (ZMod ℓ)) Γ
    (homRep (zmodRepOfTorsion ℓ T hTℓ) (zmodRepOfTorsion ℓ M hMℓ)) :=
  (quotientRep (P : Subgroup G) (homRep (zmodRepOfTorsion ℓ T hTℓ) (zmodRepOfTorsion ℓ M hMℓ))
    (homRep_ρ_of_mem P (zmodRepOfTorsion ℓ T hTℓ) (zmodRepOfTorsion ℓ M hMℓ) hT hM)).comp
    e.symm.toMonoidHom

omit [IsTopologicalGroup G] [CompactSpace G] [CompactSpace (P : Subgroup G)] [Finite Γ]
  [IsSmoothRep T] [IsSmoothRep M] in
theorem twistRep_apply (g : G) (f : homRep (zmodRepOfTorsion ℓ T hTℓ) (zmodRepOfTorsion ℓ M hMℓ)) :
    twistRep P e ℓ T M hTℓ hMℓ hT hM (e (QuotientGroup.mk g)) f =
      (homRep (zmodRepOfTorsion ℓ T hTℓ) (zmodRepOfTorsion ℓ M hMℓ)).ρ g f := by
  rw [twistRep, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
  rfl

/-- The additive function `X ↦ dim (X ⊗ Hom(T, M))^Γ` on finite `𝔽_ℓ[Γ]`-modules. -/
def twistFun [Module.Finite (ULift.{u} (ZMod ℓ))
      (homRep (zmodRepOfTorsion ℓ T hTℓ) (zmodRepOfTorsion ℓ M hMℓ))]
    (hΓ : Nat.Coprime (Nat.card Γ) ℓ) : AdditiveFunction.{u} ℓ Γ :=
  AdditiveFunction.invariantsTensorULift ℓ Γ hΓ (twistRep P e ℓ T M hTℓ hMℓ hT hM)

variable [Module.Finite (ULift.{u} (ZMod ℓ))
  (homRep (zmodRepOfTorsion ℓ T hTℓ) (zmodRepOfTorsion ℓ M hMℓ))]

omit [IsTopologicalGroup G] [CompactSpace G] [CompactSpace (P : Subgroup G)] [IsSmoothRep T]
  [IsSmoothRep M] in
theorem twistFun_apply (hΓ : Nat.Coprime (Nat.card Γ) ℓ) (X : Type u) [AddCommGroup X]
    [Module (ZMod ℓ) X] [Finite X] (ρ : Representation (ZMod ℓ) Γ X) :
    (twistFun P e ℓ T M hTℓ hMℓ hT hM hΓ).toFun X ρ = Module.finrank (ULift.{u} (ZMod ℓ))
      ((zmodRepULift.{u} ρ).tprod (twistRep P e ℓ T M hTℓ hMℓ hT hM)).invariants :=
  rfl

omit [Module.Finite (ULift.{u} (ZMod ℓ))
  (homRep (zmodRepOfTorsion ℓ T hTℓ) (zmodRepOfTorsion ℓ M hMℓ))] [CompactSpace G] [Finite Γ]
  [Fact ℓ.Prime] in
/-- The comparison of `Hⁱ(P, T)` with `Hⁱ(P, T)` over `ULift (ZMod ℓ)`, as `ℓ`-torsion. -/
theorem conj_torsNEquiv (i : ℕ) (g : G)
    (x : cohomology (Rep.res (P : Subgroup G).subtype (zmodRepOfTorsion ℓ T hTℓ)) i) :
    letI := conjAction (P : Subgroup G) e T i
    ((torsNEquivOfNsmul ℓ (nsmul_cohomology_eq_zero (Rep.res (P : Subgroup G).subtype T) hTℓ i)).symm
        ((cohomologyAddEquivOfEquiv (A := Rep.res (P : Subgroup G).subtype T)
          (A' := Rep.res (P : Subgroup G).subtype (zmodRepOfTorsion ℓ T hTℓ))
          (zmodRepOfTorsionEquiv ℓ T hTℓ) (fun _ _ => rfl) i).symm
          ((cohomologyConj (zmodRepOfTorsion ℓ T hTℓ) (P : Subgroup G) i g).hom x))) =
      torsNRep Γ _ ℓ (e (QuotientGroup.mk g))
        ((torsNEquivOfNsmul ℓ (nsmul_cohomology_eq_zero (Rep.res (P : Subgroup G).subtype T) hTℓ i)).symm
          ((cohomologyAddEquivOfEquiv (A := Rep.res (P : Subgroup G).subtype T)
            (A' := Rep.res (P : Subgroup G).subtype (zmodRepOfTorsion ℓ T hTℓ))
            (zmodRepOfTorsionEquiv ℓ T hTℓ) (fun _ _ => rfl) i).symm x)) := by
  let := conjAction (P : Subgroup G) e T i
  apply Subtype.ext
  rw [coe_torsNRep_apply]
  change (cohomologyAddEquivOfEquiv _ _ i).symm _ = e (QuotientGroup.mk g) • _
  rw [conjAction_smul]
  apply (cohomologyAddEquivOfEquiv (A := Rep.res (P : Subgroup G).subtype T)
    (A' := Rep.res (P : Subgroup G).subtype (zmodRepOfTorsion ℓ T hTℓ))
    (zmodRepOfTorsionEquiv ℓ T hTℓ) (fun _ _ => rfl) i).injective
  rw [AddEquiv.apply_symm_apply]
  have h := cohomologyAddEquivOfEquiv_cohomologyConj (A := T) (A' := zmodRepOfTorsion ℓ T hTℓ)
    (zmodRepOfTorsionEquiv ℓ T hTℓ) (fun _ _ => rfl) (P : Subgroup G) i g
    ((cohomologyAddEquivOfEquiv (A := Rep.res (P : Subgroup G).subtype T)
      (A' := Rep.res (P : Subgroup G).subtype (zmodRepOfTorsion ℓ T hTℓ))
      (zmodRepOfTorsionEquiv ℓ T hTℓ) (fun _ _ => rfl) i).symm x)
  rw [AddEquiv.apply_symm_apply] at h
  exact h.symm

/-- **Dimensions through the subgroup `P`.** `dim Hⁱ(G, M) = twistFun(Hⁱ(P, T))`, with `Γ` acting on
`Hⁱ(P, T)` by conjugation and `Hⁱ(P, T)` viewed as its own `ℓ`-torsion. -/
theorem finrank_cohomology_eq_twistFun
    (hTr : Module.finrank (ULift.{u} (ZMod ℓ)) (zmodRepOfTorsion ℓ T hTℓ) = 1)
    (hP : (((P : Subgroup G).index : ℕ) : ULift.{u} (ZMod ℓ)) ≠ 0)
    (hΓ : Nat.Coprime (Nat.card Γ) ℓ) (i : ℕ) [Finite M]
    [Finite (cohomology (Rep.res (P : Subgroup G).subtype T) i)] :
    (Module.finrank (ULift.{u} (ZMod ℓ)) (cohomology (zmodRepOfTorsion ℓ M hMℓ) i) : ℤ) =
      (letI := conjAction (P : Subgroup G) e T i;
        (twistFun P e ℓ T M hTℓ hMℓ hT hM hΓ).toFun
          (TorsN (cohomology (Rep.res (P : Subgroup G).subtype T) i) ℓ)
          (torsNRep Γ (cohomology (Rep.res (P : Subgroup G).subtype T) i) ℓ)) := by
  let := conjAction (P : Subgroup G) e T i
  have : Finite (zmodRepOfTorsion ℓ M hMℓ) := inferInstanceAs (Finite M)
  have : Module.Finite (ULift.{u} (ZMod ℓ)) (zmodRepOfTorsion ℓ M hMℓ) := Module.Finite.of_finite
  have hkey := finrank_cohomology_eq_finrank_invariants P (zmodRepOfTorsion ℓ T hTℓ)
    (zmodRepOfTorsion ℓ M hMℓ) hT hM hTr hP i
  have hc : Representation.tprod ((cohomologyConjRep (zmodRepOfTorsion ℓ T hTℓ) (P : Subgroup G) i).comp
      e.symm.toMonoidHom) (twistRep P e ℓ T M hTℓ hMℓ hT hM) =
      ((cohomologyConjRep (zmodRepOfTorsion ℓ T hTℓ) (P : Subgroup G) i).tprod
        (quotientRep (P : Subgroup G) (homRep (zmodRepOfTorsion ℓ T hTℓ) (zmodRepOfTorsion ℓ M hMℓ))
          (homRep_ρ_of_mem P (zmodRepOfTorsion ℓ T hTℓ) (zmodRepOfTorsion ℓ M hMℓ) hT hM))).comp
        e.symm.toMonoidHom := rfl
  have hinv := invariants_comp_of_surjective
    ((cohomologyConjRep (zmodRepOfTorsion ℓ T hTℓ) (P : Subgroup G) i).tprod
      (quotientRep (P : Subgroup G) (homRep (zmodRepOfTorsion ℓ T hTℓ) (zmodRepOfTorsion ℓ M hMℓ))
        (homRep_ρ_of_mem P (zmodRepOfTorsion ℓ T hTℓ) (zmodRepOfTorsion ℓ M hMℓ) hT hM)))
    e.symm.toMonoidHom e.symm.surjective
  let φ : cohomology (Rep.res (P : Subgroup G).subtype (zmodRepOfTorsion ℓ T hTℓ)) i ≃+
      TorsN (cohomology (Rep.res (P : Subgroup G).subtype T) i) ℓ :=
    (cohomologyAddEquivOfEquiv (A := Rep.res (P : Subgroup G).subtype T)
      (A' := Rep.res (P : Subgroup G).subtype (zmodRepOfTorsion ℓ T hTℓ))
      (zmodRepOfTorsionEquiv ℓ T hTℓ) (fun _ _ => rfl) i).symm.trans
      (torsNEquivOfNsmul ℓ (nsmul_cohomology_eq_zero (Rep.res (P : Subgroup G).subtype T) hTℓ i)).symm
  have hφ := finrank_invariants_tprod_eq_of_linearEquiv
    ((cohomologyConjRep (zmodRepOfTorsion ℓ T hTℓ) (P : Subgroup G) i).comp e.symm.toMonoidHom)
    (zmodRepULift.{u} (torsNRep Γ (cohomology (Rep.res (P : Subgroup G).subtype T) i) ℓ))
    (twistRep P e ℓ T M hTℓ hMℓ hT hM) (addEquivZModLinear φ) (fun γ x => by
      obtain ⟨q, rfl⟩ := e.surjective γ
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      rw [addEquivZModLinear_apply, addEquivZModLinear_apply, zmodRepULift_apply,
        MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
        cohomologyConjRep_mk]
      exact conj_torsNEquiv P e ℓ T hTℓ i g x)
  rw [twistFun_apply, hkey, ← hinv, ← hc]
  exact_mod_cast hφ

end Twist

end

end Langlands.GaloisCohomology
