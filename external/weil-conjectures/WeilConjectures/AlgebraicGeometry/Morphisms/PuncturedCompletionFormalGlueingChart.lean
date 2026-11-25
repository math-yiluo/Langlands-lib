/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedCompletionMatchingSections
public import WeilConjectures.RingTheory.FormalGlueingH0
import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedCompletionAffineDatum
import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedCompletionChartRestriction

/-! # Geometric realization of a formal glueing chart

## References

* Stacks Project, Tag 0BLH, first two proof paragraphs
* Tag 05EL, the definition of compatible sections
* Stacks Project, Tag 0BLH, first two proof paragraphs, and Tag 05EL, the displayed definition of H0
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CompletionGluingData

/-- The sheaf equalizer identifies matching sections with compatible tuples,
with the selected coordinate equal to restriction to the corresponding chart. -/
theorem exists_formalGlueingData_matching_chart
    {A : Type u} [CommRing A] [IsLocalRing A]
    {U : (Spec (.of A)).Opens}
    (hU : ∀ x : Spec (.of A), x ∈ U ↔ x ≠ IsLocalRing.closedPoint A)
    {Y : Scheme.{u}} {q : Y ⟶ U.toScheme} [IsFinite q]
    {E : Scheme.{u}} {s : E ⟶ Spec
      (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))} [IsFinite s]
    (D : CompletionGluingData A U q E s) (t : ℕ) (g : Fin t → A)
    (hgen : Ideal.span (Set.range g) = IsLocalRing.maximalIdeal A) (i : Fin t) :
    let C := AdicCompletion (IsLocalRing.maximalIdeal A) A
    let φ := algebraMap A C
    let W := (D.modelMap ∣_ U) ⁻¹ᵁ (U.ι ⁻¹ᵁ PrimeSpectrum.basicOpen (g i))
    let ρ := ((ΓSpecIso D.matchingRing).inv ≫
      (W.ι ≫ (D.modelMap ⁻¹ᵁ U).ι).appTop).hom
    let ψ := (D.puncturedMap ∣_ W).appTop.hom
    letI : Algebra A D.matchingRing := D.baseMap.hom.toAlgebra
    letI : Algebra A Γ((D.puncturedMap ⁻¹ᵁ W).toScheme, ⊤) :=
      ((ψ.comp ρ).comp D.baseMap.hom).toAlgebra
    ∃ (X : FormalGlueing.Data.{u, u, u} φ g)
      (b : FormalGlueing.h0 φ g X ≃ₗ[A] D.matchingRing)
      (c : FormalGlueing.piece (g i) (X.M i) ≃ₗ[A]
        Γ((D.puncturedMap ⁻¹ᵁ W).toScheme, ⊤)),
      ∀ h, ψ (ρ (b h)) = c (h.val.2 i) := by
  classical
  dsimp only
  let : Algebra A D.matchingRing := D.baseMap.hom.toAlgebra
  let C := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let φ := algebraMap A C
  let V : Fin t → Y.Opens := fun j ↦ (q ≫ U.ι) ⁻¹ᵁ PrimeSpectrum.basicOpen (g j)
  let aY := ((ΓSpecIso (.of A)).inv ≫ (q ≫ U.ι).appTop).hom
  let aE := ((ΓSpecIso (.of A)).inv ≫ (s ≫ completionSpecMap A).appTop).hom
  let : Algebra A Γ(Y, ⊤) := aY.toAlgebra
  let : Algebra A Γ(E, ⊤) := aE.toAlgebra
  let : ∀ j, Algebra A Γ(Y, V j) := fun j ↦
    ((Y.presheaf.map (homOfLE (le_top : V j ≤ ⊤)).op).hom.comp aY).toAlgebra
  have hdatum := D.exists_formalGlueingData_affine_datum hU t g hgen
  dsimp only at hdatum
  obtain ⟨hcover, X, e, d, hmem⟩ := hdatum
  let O := pullback q (completionSpecMap A ∣_ U)
  let p : O ⟶ Y := pullback.fst q (completionSpecMap A ∣_ U)
  let F := p.appTop
  let G := D.toCompleted.appTop
  let P : D.matchingRing ⟶ Γ(Y, ⊤) := pullback.fst F G
  let Q : D.matchingRing ⟶ Γ(E, ⊤) := pullback.snd F G
  let res (j : Fin t) : Γ(Y, ⊤) →+* Γ(Y, V j) :=
    (Y.presheaf.map (homOfLE (le_top : V j ≤ ⊤)).op).hom
  have hP : D.baseMap ≫ P = CommRingCat.ofHom aY := by
    simp only [baseMap, P, F, G, p, Category.assoc, pullback.lift_fst]
    rfl
  have hQ : D.baseMap ≫ Q = CommRingCat.ofHom aE := by
    simp only [baseMap, Q, F, G, p, Category.assoc, pullback.lift_snd]
    rfl
  let PL : D.matchingRing →ₗ[A] Γ(Y, ⊤) :=
    { toFun := P
      map_add' := P.hom.map_add
      map_smul' := fun a z ↦ by
        simp only [Algebra.smul_def, map_mul]
        congr 1
        exact ConcreteCategory.congr_hom hP a }
  let QL : D.matchingRing →ₗ[A] Γ(E, ⊤) :=
    { toFun := Q
      map_add' := Q.hom.map_add
      map_smul' := fun a z ↦ by
        simp only [Algebra.smul_def, map_mul]
        congr 1
        exact ConcreteCategory.congr_hom hQ a }
  let RL (j : Fin t) : Γ(Y, ⊤) →ₗ[A] Γ(Y, V j) :=
    { toFun := res j
      map_add' := (res j).map_add
      map_smul' := fun a z ↦ by
        simp only [Algebra.smul_def, map_mul]
        rfl }
  let r0 : D.matchingRing →ₗ[A]
      (FormalGlueing.restrict φ X.M' × ∀ j, FormalGlueing.piece (g j) (X.M j)) :=
    (e.symm.toLinearMap.comp QL).prod
      (LinearMap.pi (fun j ↦ (d j).symm.toLinearMap.comp ((RL j).comp PL)))
  have hrmem (z : D.matchingRing) : r0 z ∈ FormalGlueing.h0 φ g X := by
    apply (hmem (r0 z)).mpr
    change Y.presheaf.IsCompatible V
        (fun j ↦ d j ((d j).symm (res j (P z)))) ∧
      ∀ j, p.app (V j) (d j ((d j).symm (res j (P z)))) =
        O.presheaf.map (homOfLE (le_top : p ⁻¹ᵁ V j ≤ ⊤)).op
          (G (e (e.symm (Q z))))
    simp only [LinearEquiv.apply_symm_apply]
    constructor
    · intro j k
      change Y.presheaf.map (homOfLE (inf_le_left : V j ⊓ V k ≤ V j)).op (res j (P z)) =
        Y.presheaf.map (homOfLE (inf_le_right : V j ⊓ V k ≤ V k)).op (res k (P z))
      exact ConcreteCategory.congr_hom (show
        Y.presheaf.map (homOfLE (le_top : V j ≤ ⊤)).op ≫
            Y.presheaf.map (homOfLE (inf_le_left : V j ⊓ V k ≤ V j)).op =
          Y.presheaf.map (homOfLE (le_top : V k ≤ ⊤)).op ≫
            Y.presheaf.map (homOfLE (inf_le_right : V j ⊓ V k ≤ V k)).op by
        rw [← Functor.map_comp, ← Functor.map_comp]
        rfl) (P z)
    · intro j
      have hn := ConcreteCategory.congr_hom
        (p.naturality (homOfLE (le_top : V j ≤ ⊤)).op) (P z)
      change p.app (V j) (res j (P z)) =
        O.presheaf.map (homOfLE (le_top : p ⁻¹ᵁ V j ≤ ⊤)).op (F (P z)) at hn
      rw [hn]
      exact congrArg (O.presheaf.map (homOfLE le_top).op)
        (ConcreteCategory.congr_hom (pullback.condition (f := F) (g := G)) z)
  let r : D.matchingRing →ₗ[A] FormalGlueing.h0 φ g X := r0.codRestrict _ hrmem
  have hrprime (z : D.matchingRing) : e (r z).val.1 = Q z := by
    exact e.apply_symm_apply (Q z)
  have hrchart (z : D.matchingRing) (j : Fin t) :
      d j ((r z).val.2 j) = res j (P z) := by
    exact (d j).apply_symm_apply (res j (P z))
  let cone := CommRingCat.pullbackCone F G
  let J := (CommRingCat.pullbackConeIsLimit F G).conePointUniqueUpToIso
    (pullback.isLimit F G)
  have hJP (z : cone.pt) : P (J.hom z) = z.val.1 := by
    exact ConcreteCategory.congr_hom
      ((CommRingCat.pullbackConeIsLimit F G).conePointUniqueUpToIso_hom_comp
        (pullback.isLimit F G) WalkingCospan.left) z
  have hJQ (z : cone.pt) : Q (J.hom z) = z.val.2 := by
    exact ConcreteCategory.congr_hom
      ((CommRingCat.pullbackConeIsLimit F G).conePointUniqueUpToIso_hom_comp
        (pullback.isLimit F G) WalkingCospan.right) z
  have hJinv (z : D.matchingRing) : J.hom (J.inv z) = z := by
    exact ConcreteCategory.congr_hom J.inv_hom_id z
  have hext {z w : D.matchingRing} (hp : P z = P w) (hq : Q z = Q w) : z = w := by
    have hp' : (J.inv z).val.1 = (J.inv w).val.1 := by
      simpa only [← hJP, hJinv] using hp
    have hq' : (J.inv z).val.2 = (J.inv w).val.2 := by
      simpa only [← hJQ, hJinv] using hq
    have hh : J.inv z = J.inv w := Subtype.ext (Prod.ext hp' hq')
    simpa only [hJinv] using congrArg J.hom hh
  have hinj : Function.Injective r := by
    intro z w h
    apply hext
    · apply Y.sheaf.eq_of_locally_eq' V ⊤ (fun _ ↦ homOfLE le_top) hcover
      intro j
      exact (hrchart z j).symm.trans
        ((congrArg (fun h ↦ d j (h.val.2 j)) h).trans (hrchart w j))
    · exact (hrprime z).symm.trans ((congrArg (fun h ↦ e h.val.1) h).trans (hrprime w))
  have hsurj : Function.Surjective r := by
    intro h
    obtain ⟨hcompat, hlocal⟩ := (hmem h.val).mp h.property
    obtain ⟨a, ha, _⟩ := Y.sheaf.existsUnique_gluing' V ⊤
      (fun _ ↦ homOfLE le_top) hcover (fun j ↦ d j (h.val.2 j)) hcompat
    have hcoverO : (⊤ : O.Opens) ≤ iSup (fun j ↦ p ⁻¹ᵁ V j) := by
      intro x _
      obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp
        (hcover (show p x ∈ ⊤ from trivial))
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨j, hj⟩
    have hmatch : F a = G (e h.val.1) := by
      apply O.sheaf.eq_of_locally_eq' (fun j ↦ p ⁻¹ᵁ V j) ⊤
        (fun _ ↦ homOfLE le_top) hcoverO
      intro j
      have hn := ConcreteCategory.congr_hom
        (p.naturality (homOfLE (le_top : V j ≤ ⊤)).op) a
      change p.app (V j) (res j a) =
        O.presheaf.map (homOfLE (le_top : p ⁻¹ᵁ V j ≤ ⊤)).op (F a) at hn
      exact hn.symm.trans
        ((congrArg (p.app (V j)) (ha j)).trans (hlocal j))
    let z : cone.pt := ⟨(a, e h.val.1), hmatch⟩
    refine ⟨J.hom z, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · apply e.injective
      rw [hrprime, hJQ]
    · funext j
      apply (d j).injective
      rw [hrchart, hJP]
      exact ha j
  let b := (LinearEquiv.ofBijective r ⟨hinj, hsurj⟩).symm
  have hrestriction := D.exists_matching_chart_restriction (g i)
  dsimp only at hrestriction
  obtain ⟨c0, hc0⟩ := hrestriction
  refine ⟨X, b, (d i).trans c0, ?_⟩
  intro h
  have hb : r (b h) = h := (LinearEquiv.ofBijective r ⟨hinj, hsurj⟩).apply_symm_apply h
  exact (hc0 (b h)).trans (congrArg c0
    ((hrchart (b h) i).symm.trans (congrArg (fun h ↦ d i (h.val.2 i)) hb)))


end AlgebraicGeometry.Scheme.CompletionGluingData
