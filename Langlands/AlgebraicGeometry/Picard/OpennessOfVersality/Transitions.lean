import Langlands.AlgebraicGeometry.Picard.OpennessOfVersality.Obstruction
import Langlands.AlgebraicGeometry.Picard.OpennessOfVersality.FrameCoord

/-! # Transition functions of pulled-back frames on the test covers -/

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.OpennessOfVersality

open RelativeAffineSections CocycleGluing

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
  {P : Type u} [CommRing P] [Algebra R P] (K : (relSpace f P).OrderedAffineCover)
  {A : Type u} [CommRing A] [Algebra R A] [Algebra P A] [IsScalarTower R P A]

lemma pair_le (s : P →ₐ[R] A)
    (hs : ∀ V, relMap f s ⁻¹ᵁ V = relMap f (IsScalarTower.toAlgHom R P A) ⁻¹ᵁ V) (i j : K.ι) :
    (testCover f K A).U i ⊓ (testCover f K A).U j ≤ relMap f s ⁻¹ᵁ (K.U i ⊓ K.U j) := by
  rw [hs]
  exact le_rfl

/-- The map on sections over pairwise intersections along an algebra map. -/
def pairMapAlong (s : P →ₐ[R] A)
    (hs : ∀ V, relMap f s ⁻¹ᵁ V = relMap f (IsScalarTower.toAlgHom R P A) ⁻¹ᵁ V) (i j : K.ι) :
    Γ(relSpace f P, K.U i ⊓ K.U j) ⟶
      Γ(relSpace f A, (testCover f K A).U i ⊓ (testCover f K A).U j) :=
  (relMap f s).appLE _ _ (pair_le f K s hs i j)

/-- A family of units on the pairwise intersections, pushed along an algebra map. -/
def pairUnitsAlong (s : P →ₐ[R] A)
    (hs : ∀ V, relMap f s ⁻¹ᵁ V = relMap f (IsScalarTower.toAlgHom R P A) ⁻¹ᵁ V)
    (g : ∀ i j : K.ι, (Γ(relSpace f P, K.U i ⊓ K.U j))ˣ) (i j : K.ι) :
    (Γ(relSpace f A, (testCover f K A).U i ⊓ (testCover f K A).U j))ˣ :=
  Units.map (pairMapAlong f K s hs i j).hom.toMonoidHom (g i j)

lemma pr_pairMapAlong (s : P →ₐ[R] A)
    (hs : ∀ V, relMap f s ⁻¹ᵁ V = relMap f (IsScalarTower.toAlgHom R P A) ⁻¹ᵁ V)
    (u : ∀ i j : K.ι, Γ(relSpace f P, K.U i ⊓ K.U j)) {p : ℕ} (σ : K.Idx p) (a b : Fin (p + 1)) :
    pr (testCover f K A) (fun i j => (pairMapAlong f K s hs i j).hom (u i j)) σ a b =
      (secMapAlong f K s hs σ).hom (pr K u σ a b) := by
  unfold pr pairMapAlong secMapAlong
  change ((relMap f s).appLE _ _ _ ≫ (relSpace f A).presheaf.map _).hom _ =
    ((relSpace f P).presheaf.map _ ≫ (relMap f s).appLE _ _ _).hom _
  rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]

lemma pr_pairUnitsAlong_val (s : P →ₐ[R] A)
    (hs : ∀ V, relMap f s ⁻¹ᵁ V = relMap f (IsScalarTower.toAlgHom R P A) ⁻¹ᵁ V)
    (g : ∀ i j : K.ι, (Γ(relSpace f P, K.U i ⊓ K.U j))ˣ) {p : ℕ} (σ : K.Idx p)
    (a b : Fin (p + 1)) :
    pr (testCover f K A) (uval (testCover f K A) (pairUnitsAlong f K s hs g)) σ a b =
      (secMapAlong f K s hs σ).hom (pr K (uval K g) σ a b) :=
  pr_pairMapAlong f K s hs (uval K g) σ a b

lemma pr_pairUnitsAlong_inv (s : P →ₐ[R] A)
    (hs : ∀ V, relMap f s ⁻¹ᵁ V = relMap f (IsScalarTower.toAlgHom R P A) ⁻¹ᵁ V)
    (g : ∀ i j : K.ι, (Γ(relSpace f P, K.U i ⊓ K.U j))ˣ) {p : ℕ} (σ : K.Idx p)
    (a b : Fin (p + 1)) :
    pr (testCover f K A) (uinv (testCover f K A) (pairUnitsAlong f K s hs g)) σ a b =
      (secMapAlong f K s hs σ).hom (pr K (uinv K g) σ a b) :=
  pr_pairMapAlong f K s hs (uinv K g) σ a b

section Pull

variable {A₀ : Type u} [CommRing A₀] [Algebra R A₀] [Algebra P A₀] [IsScalarTower R P A₀]

lemma testCover_le_preimage (χ : A₀ →ₐ[R] A)
    (hs : ∀ V, relMap f (χ.comp (IsScalarTower.toAlgHom R P A₀)) ⁻¹ᵁ V =
      relMap f (IsScalarTower.toAlgHom R P A) ⁻¹ᵁ V) (i : K.ι) :
    (testCover f K A).U i ≤ relMap f χ ⁻¹ᵁ (testCover f K A₀).U i := by
  change relMap f (IsScalarTower.toAlgHom R P A) ⁻¹ᵁ K.U i ≤
    relMap f χ ⁻¹ᵁ (relMap f (IsScalarTower.toAlgHom R P A₀) ⁻¹ᵁ K.U i)
  rw [← Scheme.Hom.comp_preimage, ← relMap_comp, hs]

/-- The restricted pullbacks of frames with transition functions given by a family pushed to
`relSpace f A₀` have the transition functions pushed to `relSpace f A`. -/
lemma isTransition_pullback_res {C : (relSpace f A₀).Modules}
    (e : ∀ i, Γ(C, (testCover f K A₀).U i)) (g : ∀ i j : K.ι, (Γ(relSpace f P, K.U i ⊓ K.U j))ˣ)
    (hge : IsTransition e (pairUnitsAlong f K (IsScalarTower.toAlgHom R P A₀) (fun _ => rfl) g))
    (χ : A₀ →ₐ[R] A)
    (hs : ∀ V, relMap f (χ.comp (IsScalarTower.toAlgHom R P A₀)) ⁻¹ᵁ V =
      relMap f (IsScalarTower.toAlgHom R P A) ⁻¹ᵁ V) :
    IsTransition (T := (testCover f K A).U)
      (fun i => ((Scheme.Modules.pullback (relMap f χ)).obj C).presheaf.map
        (homOfLE (testCover_le_preimage f K χ hs i)).op
          (Scheme.Modules.pullbackLocalSection (relMap f χ) (e i)))
      (pairUnitsAlong f K (χ.comp (IsScalarTower.toAlgHom R P A₀)) hs g) := by
  intro i j
  have hW : (testCover f K A).U i ⊓ (testCover f K A).U j ≤
      relMap f χ ⁻¹ᵁ (testCover f K A₀).U i ⊓ relMap f χ ⁻¹ᵁ (testCover f K A₀).U j :=
    inf_le_inf (testCover_le_preimage f K χ hs i) (testCover_le_preimage f K χ hs j)
  have h := congrArg (fun z => ((Scheme.Modules.pullback (relMap f χ)).obj C).presheaf.map
    (homOfLE hW).op z) (LineHom.isTransition_pullback (relMap f χ) hge i j)
  have hv : (relSpace f A).presheaf.map (homOfLE hW).op
      ((CocycleGluing.pullbackCocycle (relMap f χ)
        (pairUnitsAlong f K (IsScalarTower.toAlgHom R P A₀) (fun _ => rfl) g) i j :
          Γ(relSpace f A, _))) =
      (pairUnitsAlong f K (χ.comp (IsScalarTower.toAlgHom R P A₀)) hs g i j :
        Γ(relSpace f A, _)) := by
    change ((pairMapAlong f K (IsScalarTower.toAlgHom R P A₀) (fun _ => rfl) i j ≫
      (relMap f χ).appLE _ _ le_rfl) ≫ (relSpace f A).presheaf.map (homOfLE hW).op).hom
        (g i j : Γ(relSpace f P, K.U i ⊓ K.U j)) =
      (pairMapAlong f K (χ.comp (IsScalarTower.toAlgHom R P A₀)) hs i j).hom (g i j)
    rw [pairMapAlong, pairMapAlong, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_map]
    exact congrArg (fun φ : Γ(relSpace f P, K.U i ⊓ K.U j) ⟶
        Γ(relSpace f A, (testCover f K A).U i ⊓ (testCover f K A).U j) => φ.hom (g i j))
      (appLE_congr (relMap_comp f _ χ).symm _ _ _ _)
  simp only [res_res, Scheme.Modules.map_smul] at h ⊢
  rw [hv] at h
  exact h

end Pull

section Push

variable {Y : Scheme.{u}}

/-- A family of units on the pairwise intersections of `K`, pushed along `w : Y ⟶ relSpace f P`
to a family of opens `W` of `Y` with `W i ⊓ W j ≤ w ⁻¹ᵁ (K.U i ⊓ K.U j)`. -/
def pushUnits (w : Y ⟶ relSpace f P) (W : K.ι → Y.Opens)
    (hW : ∀ i j, W i ⊓ W j ≤ w ⁻¹ᵁ (K.U i ⊓ K.U j))
    (g : ∀ i j : K.ι, (Γ(relSpace f P, K.U i ⊓ K.U j))ˣ) (i j : K.ι) : (Γ(Y, W i ⊓ W j))ˣ :=
  Units.map (w.appLE _ _ (hW i j)).hom.toMonoidHom (g i j)

lemma pushUnits_congr {w w' : Y ⟶ relSpace f P} (hw : w = w') (W : K.ι → Y.Opens)
    (hW : ∀ i j, W i ⊓ W j ≤ w ⁻¹ᵁ (K.U i ⊓ K.U j))
    (hW' : ∀ i j, W i ⊓ W j ≤ w' ⁻¹ᵁ (K.U i ⊓ K.U j))
    (g : ∀ i j : K.ι, (Γ(relSpace f P, K.U i ⊓ K.U j))ˣ) :
    pushUnits f K w W hW g = pushUnits f K w' W hW' g := by
  subst hw
  rfl

/-- Frames pulled back along `v : Y ⟶ Z'` and restricted to opens `W i`, from frames whose
transition functions are pushed along `w : Z' ⟶ relSpace f P`, have the transition functions
pushed along `v ≫ w`. -/
lemma isTransition_pullback_push {Z' : Scheme.{u}} {C : Z'.Modules} (w : Z' ⟶ relSpace f P)
    (T : K.ι → Z'.Opens) (hT : ∀ i j, T i ⊓ T j ≤ w ⁻¹ᵁ (K.U i ⊓ K.U j))
    (e : ∀ i, Γ(C, T i)) (g : ∀ i j : K.ι, (Γ(relSpace f P, K.U i ⊓ K.U j))ˣ)
    (hge : IsTransition e (pushUnits f K w T hT g)) (v : Y ⟶ Z') (W : K.ι → Y.Opens)
    (hWT : ∀ i, W i ≤ v ⁻¹ᵁ T i) (hW : ∀ i j, W i ⊓ W j ≤ (v ≫ w) ⁻¹ᵁ (K.U i ⊓ K.U j)) :
    IsTransition (T := W)
      (fun i => ((Scheme.Modules.pullback v).obj C).presheaf.map (homOfLE (hWT i)).op
        (Scheme.Modules.pullbackLocalSection v (e i)))
      (pushUnits f K (v ≫ w) W hW g) := by
  intro i j
  have hWW : W i ⊓ W j ≤ v ⁻¹ᵁ T i ⊓ v ⁻¹ᵁ T j := inf_le_inf (hWT i) (hWT j)
  have h := congrArg (fun z => ((Scheme.Modules.pullback v).obj C).presheaf.map
    (homOfLE hWW).op z) (LineHom.isTransition_pullback v hge i j)
  have hv : Y.presheaf.map (homOfLE hWW).op
      ((CocycleGluing.pullbackCocycle v (pushUnits f K w T hT g) i j : Γ(Y, _))) =
      (pushUnits f K (v ≫ w) W hW g i j : Γ(Y, _)) := by
    change ((w.appLE _ _ (hT i j) ≫ v.appLE _ _ le_rfl) ≫ Y.presheaf.map (homOfLE hWW).op).hom
        (g i j : Γ(relSpace f P, K.U i ⊓ K.U j)) = ((v ≫ w).appLE _ _ (hW i j)).hom (g i j)
    rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_map]
  simp only [res_res, Scheme.Modules.map_smul] at h ⊢
  rw [hv] at h
  exact h

/-- An isomorphism of module sheaves preserves transition relations. -/
lemma isTransition_map {M M' : Y.Modules} {ι : Type u} {W : ι → Y.Opens} {s : ∀ i, Γ(M, W i)}
    {g : ∀ i j : ι, (Γ(Y, W i ⊓ W j))ˣ} (h : IsTransition s g) (φ : M ⟶ M') :
    IsTransition (fun i => φ.app (W i) (s i)) g := by
  intro i j
  rw [← app_res, ← app_res, h i j, Scheme.Modules.Hom.app_smul]

end Push

end Langlands.AlgebraicGeometry.Picard.OpennessOfVersality
