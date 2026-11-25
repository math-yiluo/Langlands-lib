/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
import WeilConjectures.AlgebraicGeometry.Curve.DenseOpenFiniteComplement
import WeilConjectures.AlgebraicGeometry.EtaleModulePullbackForgetNaturality
import WeilConjectures.AlgebraicGeometry.Curve.PrimeAnnihilatedPrimaryCases
import WeilConjectures.AlgebraicGeometry.Curve.PrimeAnnihilatedInvertibleCases
import WeilConjectures.AlgebraicGeometry.Sites.FiniteSupport
import WeilConjectures.SixFunctors.Etale.Gabber
import WeilConjectures.AlgebraicGeometry.PullbackCohomologyLongExactLadder
import WeilConjectures.AlgebraicGeometry.Curve.DenseOpenClosedTerm
import WeilConjectures.AlgebraicGeometry.Curve.DenseOpenBaseChangeBoundary
import Mathlib.Algebra.FiveLemma
import WeilConjectures.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections

/-! # Descent across a finite-support cokernel

Source: Stacks Project, Tags 0A3Q and 0GJA, normalization and dense-open comparison.
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry
open Etale
variable (Λ : Type (u + 1)) [CommRing Λ]

private theorem annihilated_of_mono {X : Scheme.{u}}
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (α : F ⟶ G) [Mono α] (ℓ : ℕ) (hG : ℓ • 𝟙 G = 0) : ℓ • 𝟙 F = 0 := by
  apply (cancel_mono α).mp
  simp only [Preadditive.nsmul_comp, Category.id_comp, zero_comp]
  rw [← Category.comp_id α, ← Preadditive.comp_nsmul, hG, comp_zero]

private theorem annihilated_of_epi {X : Scheme.{u}}
    {G Q : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (β : G ⟶ Q) [Epi β] (ℓ : ℕ) (hG : ℓ • 𝟙 G = 0) : ℓ • 𝟙 Q = 0 := by
  apply (cancel_epi β).mp
  simp only [Preadditive.comp_nsmul, Category.comp_id, comp_zero]
  rw [← Category.id_comp β, ← Preadditive.nsmul_comp, hG, zero_comp]

private theorem pulled_support_isZero {X Y : Scheme.{u}} (a : Y ⟶ X)
    (V : X.Opens) (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hQ : IsZero (((V.ι)^*[AddCommGrpCat.{u + 1}]).obj Q)) :
    IsZero (((a ⁻¹ᵁ V).ι)^*[AddCommGrpCat.{u + 1}].obj
      ((a)^*[AddCommGrpCat.{u + 1}].obj Q)) := by
  let U := a ⁻¹ᵁ V
  let b := IsOpenImmersion.lift V.ι (U.ι ≫ a) (by
    rintro _ ⟨x, rfl⟩
    exact ⟨⟨a x.1, x.2⟩, rfl⟩)
  have hb : b ≫ V.ι = U.ι ≫ a := IsOpenImmersion.lift_fac _ _ _
  have hzcomp := ((b)^*[AddCommGrpCat.{u + 1}]).map_isZero hQ
  have hzcomp' : IsZero (((U.ι ≫ a)^*[AddCommGrpCat.{u + 1}]).obj Q) :=
    hzcomp.of_iso ((upperStarComp AddCommGrpCat.{u + 1} b V.ι
      (U.ι ≫ a) hb.symm).app _)
  exact hzcomp'.of_iso ((upperStarComp AddCommGrpCat.{u + 1} U.ι a).app _).symm

private theorem finite_support_high_comparison {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve f]
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (α : F ⟶ G) [Mono α] (V : X.Opens) (hV : Dense (V : Set X))
    (hQ : IsZero (((V.ι)^*[ModuleCat.{u + 1} Λ]).obj (cokernel α))) :
    let A := sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
    (∀ q : ℕ, 1 < q → Function.Bijective (Sheaf.H.map (A.map α) q)) ∧
      (∀ {W : Scheme.{u}} (a : W ⟶ X) [IsOpenImmersion a],
        Function.Bijective
          (Sheaf.H.map (((a)^*[AddCommGrpCat.{u + 1}]).map (A.map α)) 2)) := by
  let A := sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  have : A.Additive := { map_add := by intros; rfl }
  let S := ShortComplex.mk α (cokernel.π α) (cokernel.condition α)
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel α) inferInstance inferInstance
  have hT := shortExact_map_forget₂ Λ hS
  have : Mono (A.map α) := hT.mono_f
  obtain ⟨hfin, hcl, hsep⟩ := IsCurve.dense_open_finite_complement f V hV
  obtain ⟨e⟩ := exists_upperStar_forget₂_natIso Λ V.ι
  have hz : IsZero (((V.ι)^*[AddCommGrpCat.{u + 1}]).obj (A.obj (cokernel α))) :=
    (Functor.map_isZero (sheafCompose _
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})) hQ).of_iso
        (e.app (cokernel α)).symm
  refine ⟨?_, ?_⟩
  · intro q hq
    obtain ⟨n, rfl⟩ : ∃ n, q = n + 2 := ⟨q - 2, by omega⟩
    have : Subsingleton (Sheaf.H (S.map A).X₃ (n + 1)) :=
      subsingleton_H_of_isZero_upperStar V hfin hcl hsep _ hz n
    have : Subsingleton (Sheaf.H (S.map A).X₃ (n + 2)) :=
      subsingleton_H_of_isZero_upperStar V hfin hcl hsep _ hz (n + 1)
    exact Sheaf.H.bijective_map_f hT (n + 1)
  · intro W a _
    let U := a ⁻¹ᵁ V
    have hfin' : (U : Set W)ᶜ.Finite :=
      hfin.preimage a.isOpenEmbedding.injective.injOn
    have hcl' (x : W) (hx : x ∉ U) : IsClosed ({x} : Set W) := by
      have heq : a ⁻¹' {a x} = {x} := by
        ext y
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
        exact a.isOpenEmbedding.injective.eq_iff
      rw [← heq]
      exact (hcl (a x) hx).preimage a.continuous
    have hsep' (x : W) (hx : x ∉ U) : IsSepClosed (W.residueField x) := by
      have := hsep (a x) hx
      exact IsSepClosed.of_ringEquiv (asIso (a.residueFieldMap x)).commRingCatIsoToRingEquiv
    have hz' := pulled_support_isZero a V (A.obj (cokernel α)) hz
    let R := (S.map A).map ((a)^*[AddCommGrpCat.{u + 1}])
    have hR : R.ShortExact := hT.map_of_exact _
    have : Subsingleton (Sheaf.H R.X₃ 1) :=
      subsingleton_H_of_isZero_upperStar U hfin' hcl' hsep' _ hz' 0
    have : Subsingleton (Sheaf.H R.X₃ 2) :=
      subsingleton_H_of_isZero_upperStar U hfin' hcl' hsep' _ hz' 1
    exact Sheaf.H.bijective_map_f hR 1

private theorem finite_first {X : Scheme.{u}}
    {S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})}
    (hS : S.ShortExact) (hQ : Finite (Sheaf.H S.X₃ 0))
    (hvan : ∀ n, Subsingleton (Sheaf.H S.X₃ (n + 1)))
    (hG : ∀ q, Finite (Sheaf.H S.X₂ q)) (q : ℕ) : Finite (Sheaf.H S.X₁ q) := by
  cases q with
  | zero =>
    have := hG 0
    have := hS.mono_f
    exact Finite.of_injective (Sheaf.H.map S.f 0)
      (Abelian.Ext.postcomp_mk₀_injective_of_mono _ S.f)
  | succ q =>
    have hQq : Finite (Sheaf.H S.X₃ q) := by
      cases q with
      | zero => exact hQ
      | succ n =>
        have := hvan n
        infer_instance
    have := hQq
    have := hG (q + 1)
    let T := ShortComplex.mk
      (AddCommGrpCat.ofHom (Sheaf.H.δSucc hS q))
      (AddCommGrpCat.ofHom (Sheaf.H.map S.f (q + 1)))
      (by
        apply ConcreteCategory.hom_ext
        intro x
        exact (Sheaf.H.exact_δSucc_map hS q _).mpr ⟨x, rfl⟩)
    exact ((ShortComplex.ab_exact_iff_function_exact T).mpr
      (Sheaf.H.exact_δSucc_map hS q)).ab_finite

private theorem finite_support_boundary_comparison {k k' : Type u}
    [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k']
    {X X' : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve f]
    {ι : Spec (.of k') ⟶ Spec (.of k)} {f' : X' ⟶ Spec (.of k')}
    {ι' : X' ⟶ X} (h : IsPullback ι' f' f ι)
    (Q : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (V : X.Opens) (hV : Dense (V : Set X))
    (hQ : IsZero (((V.ι)^*[ModuleCat.{u + 1} Λ]).obj Q)) :
    let A := sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
    Function.Bijective (cohomologyMap ι' (A.obj Q) 0) := by
  let A := sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  have : A.Additive := { map_add := by intros; rfl }
  obtain ⟨B, b, w, hS, hB, _, _⟩ := IsCurve.dense_open_closed_term Λ f h Q V hV
  let S := ShortComplex.mk _ b w
  have hz : IsZero S.X₁ := A.map_isZero
    ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) V.ι).map_isZero hQ)
  have : IsIso b := hS.isIso_g_iff.mpr hz
  let e := asIso b
  have hc :
      (Sheaf.H.map (((ι')^*[AddCommGrpCat.{u + 1}]).map b) 0) ∘
        (cohomologyMap ι' (A.obj Q) 0) =
      (cohomologyMap ι' B 0) ∘ (Sheaf.H.map b 0) := by
    funext x
    exact (cohomologyMap_map ι' 0 b x).symm
  have hi : Function.Bijective (Sheaf.H.map b 0) :=
    (Iso.addCommGroupIsoToAddEquiv ((Sheaf.functorH _ 0).mapIso e)).bijective
  have hj : Function.Bijective
      (Sheaf.H.map (((ι')^*[AddCommGrpCat.{u + 1}]).map b) 0) :=
    (Iso.addCommGroupIsoToAddEquiv
      ((Sheaf.functorH _ 0).mapIso (((ι')^*[AddCommGrpCat.{u + 1}]).mapIso e))).bijective
  exact (Function.Bijective.of_comp_iff' hj _).mp (hc.symm ▸ hB.comp hi)

private theorem bijective_first {X Y : Scheme.{u}} (a : Y ⟶ X)
    {S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})}
    (hS : S.ShortExact)
    (hG : ∀ q, Function.Bijective (cohomologyMap a S.X₂ q))
    (hQ : ∀ q, Function.Bijective (cohomologyMap a S.X₃ q)) (q : ℕ) :
    Function.Bijective (cohomologyMap a S.X₁ q) := by
  obtain ⟨hY, δX, δY, _, _, hiX, hiY, exX, exY, c₁, c₂, c₃⟩ :=
    pullbackCohomology_longExact_ladder a S hS
  have hc₁ (n : ℕ) :
      (Sheaf.H.map (((a)^*[AddCommGrpCat.{u + 1}]).map S.f) n).comp
        (cohomologyMap a S.X₁ n) =
      (cohomologyMap a S.X₂ n).comp (Sheaf.H.map S.f n) :=
    AddMonoidHom.ext (fun x ↦ (c₁ n x).symm)
  have hc₂ (n : ℕ) :
      (Sheaf.H.map (((a)^*[AddCommGrpCat.{u + 1}]).map S.g) n).comp
        (cohomologyMap a S.X₂ n) =
      (cohomologyMap a S.X₃ n).comp (Sheaf.H.map S.g n) :=
    AddMonoidHom.ext (fun x ↦ (c₂ n x).symm)
  have hc₃ (n : ℕ) :
      (δY n).comp (cohomologyMap a S.X₃ n) =
      (cohomologyMap a S.X₁ (n + 1)).comp (δX n) :=
    AddMonoidHom.ext (fun x ↦ (c₃ n x).symm)
  cases q with
  | zero =>
    exact AddMonoidHom.bijective_of_bijective_of_injective_of_left_exact
      _ _ _ _ _ _ _ (hc₁ 0) (hc₂ 0) (exX 0).1 (exY 0).1
      (hG 0) (hQ 0).1 hiX hiY
  | succ n =>
    exact AddMonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
      _ _ _ _ _ _ _ _ _ _ _ _ _ (hc₂ n) (hc₃ n) (hc₁ (n + 1)) (hc₂ (n + 1))
      (exX n).2.1 (exX n).2.2 (exX (n + 1)).1
      (exY n).2.1 (exY n).2.2 (exY (n + 1)).1
      (hG n).2 (hQ n) (hG (n + 1)) (hQ (n + 1)).1

/-- A constructible prime-annihilated sheaf with the eight curve assertions transfers
those assertions to a subsheaf whose cokernel vanishes on a dense open.
Source: Stacks Project, Tags 0A3Q, proof, and 0GJA, proof, remarks (a)--(d).
(blueprint: b3-finite-support-mono-assertions)

Proof: The dense-open complement in a finite-type curve is zero-dimensional. The
constructible cokernel, annihilated by ℓ, has finite stalks since Λ/(ℓ) is finite.
It is the closed direct image of its restriction to that complement. Finite direct
image and zero-dimensional cohomology show that it and its pullbacks have zero
positive cohomology, finite degree-zero cohomology, and bijective field-extension maps.
The short exact sequence gives isomorphisms from F to G in degrees at least two,
the exact sequence 0 → H⁰(F) → H⁰(G) → H⁰(Q) → H¹(F) → H¹(G) → 0.
These prove C1, C2 and finiteness. For C3 and C6, if ℓ equals the characteristic
use the primary branch, and otherwise use the invertible-order branch. If a
conditional hypothesis on F has the opposite torsion type, F is zero: stalks are
annihilated by two coprime integers. For C6, when ℓ differs from the characteristic
G has invertible torsion;
when ℓ equals the characteristic and F has invertible torsion, F is zero.
For C6 and C7, degree zero is the kernel of H⁰(G) → H⁰(Q). In degree one use
0 → coker(H⁰(G) → H⁰(Q)) → H¹(F) → H¹(G) → 0 and the short five lemma.
The bijective comparisons for G and Q give both kernel and cokernel comparisons;
in higher degrees use the isomorphisms with G. For C7 use properness of X.
For C8 lift a degree-two class using G, identify H²(F) with H²(G), and use
injectivity of H² of the pulled-back inclusion, since H¹ of the pulled-back Q is zero.
Empty complements, empty curves, and the zero coefficient quotient obey the same argument. -/
theorem IsCurve.Assertions.of_finite_support_mono {k : Type u} [Field k]
    [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve f]
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (α : F ⟶ G) [Mono α] [Scheme.IsConstructibleSheaf G]
    [Scheme.IsConstructibleSheaf (cokernel α)] (ℓ : ℕ) [Fact ℓ.Prime]
    [Finite (Λ ⧸ Ideal.span {(ℓ : Λ)})]
    (hℓ : ℓ • 𝟙 G = 0)
    (V : X.Opens) (hV : Dense (V : Set X))
    (hQ : IsZero (((V.ι)^*[ModuleCat.{u + 1} Λ]).obj (cokernel α)))
    (H : IsCurve.Assertions Λ f G) : IsCurve.Assertions Λ f F := by
  classical
  let A := sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  have : A.Additive := { map_add := by intros; rfl }
  let S := ShortComplex.mk α (cokernel.π α) (cokernel.condition α)
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel α) inferInstance inferInstance
  have hT := shortExact_map_forget₂ Λ hS
  have hFℓ := annihilated_of_mono Λ α ℓ hℓ
  have hQℓ := annihilated_of_epi Λ (cokernel.π α) ℓ hℓ
  have hQ₀ := IsCurve.finite_support_prime_global_sections Λ f (cokernel α) ℓ hQℓ V hV hQ
  obtain ⟨e⟩ := exists_upperStar_forget₂_natIso Λ V.ι
  have hz : IsZero (((V.ι)^*[AddCommGrpCat.{u + 1}]).obj (A.obj (cokernel α))) :=
    (Functor.map_isZero (sheafCompose _
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})) hQ).of_iso
        (e.app (cokernel α)).symm
  obtain ⟨hfin, hcl, hsep⟩ := IsCurve.dense_open_finite_complement f V hV
  have hvan (n : ℕ) : Subsingleton (Sheaf.H (A.obj (cokernel α)) (n + 1)) :=
    subsingleton_H_of_isZero_upperStar V hfin hcl hsep _ hz n
  obtain ⟨hhigh, hopen⟩ := finite_support_high_comparison Λ f α V hV hQ
  have hzero (hF : IsZero F) (q : ℕ) : Subsingleton (Sheaf.H (A.obj F) q) :=
    Sheaf.subsingleton_H_of_isZero (A.map_isZero hF) q
  have hzeroMap (hF : IsZero F) {Y : Scheme.{u}} (a : Y ⟶ X) (q : ℕ) :
      Function.Bijective (cohomologyMap a (A.obj F) q) := by
    have := hzero hF q
    have := Sheaf.subsingleton_H_of_isZero
      (((a)^*[AddCommGrpCat.{u + 1}]).map_isZero (A.map_isZero hF)) q
    exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun y ↦ ⟨0, Subsingleton.elim _ _⟩⟩
  have compare (k' : Type u) [Field k'] [IsAlgClosed k'] {X' : Scheme.{u}}
      {ι : Spec (.of k') ⟶ Spec (.of k)} {f' : X' ⟶ Spec (.of k')}
      {ι' : X' ⟶ X} (h : IsPullback ι' f' f ι)
      (hG : ∀ q, Function.Bijective (cohomologyMap ι' (A.obj G) q)) (q : ℕ) :
      Function.Bijective (cohomologyMap ι' (A.obj F) q) := by
    have hQmap (n : ℕ) : Function.Bijective (cohomologyMap ι' (A.obj (cokernel α)) n) := by
      cases n with
      | zero => exact finite_support_boundary_comparison Λ f h (cokernel α) V hV hQ
      | succ n =>
        obtain ⟨hfin', hcl', hsep'⟩ := IsCurve.dense_open_baseChange_boundary f h V hV
        have := hvan n
        have := subsingleton_H_of_isZero_upperStar (ι' ⁻¹ᵁ V) hfin' hcl' hsep' _
          (pulled_support_isZero ι' V (A.obj (cokernel α)) hz) n
        exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun y ↦ ⟨0, Subsingleton.elim _ _⟩⟩
    exact bijective_first ι' hT hG hQmap q
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q hq
    have := H.subsingleton_of_two_lt q hq
    exact (hhigh q (by omega)).injective.subsingleton
  · intro _ q hq
    have := H.subsingleton_of_one_lt_of_isAffine q hq
    exact (hhigh q hq).injective.subsingleton
  · intro p _ _ hp q hq
    by_cases hℓp : ℓ = p
    · subst p
      have hGprim := (Scheme.prime_annihilated_primary_cases Λ ℓ G hℓ).1
      have := H.subsingleton_of_one_lt_of_isPrimaryTorsionSheaf ℓ hGprim q hq
      exact (hhigh q hq).injective.subsingleton
    · exact hzero ((Scheme.prime_annihilated_primary_cases Λ ℓ F hFℓ).2 p hℓp hp) q
  · intro _ hi q
    by_cases hu : IsUnit (ℓ : Γ(Spec (.of k), ⊤))
    · have := (Scheme.prime_annihilated_invertible_cases Λ (k := k) ℓ G hℓ).1 hu
      exact finite_first hT hQ₀ hvan (fun n ↦ H.finite_of_isTorsionSheafOfInvertibleOrder n) q
    · have := hzero
        ((Scheme.prime_annihilated_invertible_cases Λ (k := k) ℓ F hFℓ).2 hu hi) q
      infer_instance
  · intro _ _ q
    exact finite_first hT hQ₀ hvan (fun n ↦ H.finite_of_isProper n) q
  · intro hi k' _ _ X' ι f' ι' h q
    by_cases hu : IsUnit (ℓ : Γ(Spec (.of k), ⊤))
    · have := (Scheme.prime_annihilated_invertible_cases Λ (k := k) ℓ G hℓ).1 hu
      exact compare k' h
        (fun n ↦ H.bijective_cohomologyMap_of_isTorsionSheafOfInvertibleOrder k' h n) q
    · exact hzeroMap
        ((Scheme.prime_annihilated_invertible_cases Λ (k := k) ℓ F hFℓ).2 hu hi) ι' q
  · intro _ k' _ _ X' ι f' ι' h q
    exact compare k' h (fun n ↦ H.bijective_cohomologyMap_of_isProper k' h n) q
  · intro W a _ y
    obtain ⟨x, hx⟩ := H.surjective_cohomologyMap_of_isOpenImmersion a
      (Sheaf.H.map (((a)^*[AddCommGrpCat.{u + 1}]).map (A.map α)) 2 y)
    obtain ⟨z, hz⟩ := (hhigh 2 (by decide)).surjective x
    refine ⟨z, (hopen a).injective ?_⟩
    rw [← cohomologyMap_map a 2 (A.map α) z, hz, hx]

end AlgebraicGeometry
