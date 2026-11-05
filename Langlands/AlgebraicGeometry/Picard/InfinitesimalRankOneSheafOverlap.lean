import Langlands.AlgebraicGeometry.Picard.InfinitesimalRankOneSheaf
import Langlands.AlgebraicGeometry.Modules.AffineCompositeTrivialization

/-! # Common-overlap coherence for the actual patched rank-one sheaf -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard.InfinitesimalRankOneSheafOverlap

open InfinitesimalRankOnePatching InfinitesimalRankOneSheaf
open Langlands.Scheme.Modules

variable {R A B C : CommRingCat.{u}} [Algebra R A] [Algebra R B]
  (a : A →+* C) (b : B →+* C)
  (h : IsPullback (CommRingCat.ofHom (algebraMap R A))
    (CommRingCat.ofHom (algebraMap R B)) (CommRingCat.ofHom a) (CommRingCat.ofHom b))

/-- The actual coefficient map to the common overlap, using the first factorization. -/
abbrev overlapMap : R ⟶ C :=
  CommRingCat.ofHom (algebraMap R A) ≫ CommRingCat.ofHom a

/-- The first ordinary pullback trivialization transported to the common overlap. -/
def firstOverlapIso (c : Cˣ) (v : Bˣ) (hv : Units.map b.toMonoidHom v = c) :=
  affineCompositeUnitIso (R := R) (A := A) (C := C)
    (CommRingCat.ofHom (algebraMap R A)) (CommRingCat.ofHom a)
    (overlapMap a) rfl (ModuleCat.of R (patchedModule a b h c))
    (firstPullbackIso a b h c v hv)

/-- The second ordinary pullback trivialization transported along the same coefficient map. -/
def secondOverlapIso (c : Cˣ) (v : Bˣ) (hv : Units.map b.toMonoidHom v = c) :=
  affineCompositeUnitIso (R := R) (A := B) (C := C)
    (CommRingCat.ofHom (algebraMap R B)) (CommRingCat.ofHom b)
    (overlapMap a) h.w.symm (ModuleCat.of R (patchedModule a b h c))
    (secondPullbackIso a b h c v hv)

private lemma firstOverlapIso_eq (c : Cˣ) (v : Bˣ)
    (hv : Units.map b.toMonoidHom v = c) :
    firstOverlapIso a b h c v hv =
      affineCompositeUnitIso (R := R) (A := A) (C := C)
        (CommRingCat.ofHom (algebraMap R A)) (CommRingCat.ofHom a)
        (overlapMap a) rfl (ModuleCat.of R (patchedModule a b h c))
        (firstPullbackIso a b h c v hv) := rfl

private lemma secondOverlapIso_eq (c : Cˣ) (v : Bˣ)
    (hv : Units.map b.toMonoidHom v = c) :
    secondOverlapIso a b h c v hv =
      affineCompositeUnitIso (R := R) (A := B) (C := C)
        (CommRingCat.ofHom (algebraMap R B)) (CommRingCat.ofHom b)
        (overlapMap a) h.w.symm (ModuleCat.of R (patchedModule a b h c))
        (secondPullbackIso a b h c v hv) := rfl

attribute [local irreducible] affineCompositeUnitIso compositeUnitIso firstOverlapIso secondOverlapIso

/-- On every open, the first overlap adjoint has the actual first-coordinate formula. -/
private lemma firstOverlapComposite_adjoint_toOpen (c : Cˣ) (v : Bˣ)
    (hv : Units.map b.toMonoidHom v = c) (U : (Spec R).Opens)
    (z : patchedModule a b h c) :
    (tildePullbackAdjoint (R := R) (A := C) (overlapMap a)
      (M := ModuleCat.of R (patchedModule a b h c))
      (N := SheafOfModules.unit (Spec C).ringCatSheaf) (affineCompositeUnitIso (R := R) (A := A) (C := C)
        (CommRingCat.ofHom (algebraMap R A)) (CommRingCat.ofHom a)
        (overlapMap a) rfl (ModuleCat.of R (patchedModule a b h c))
        (firstPullbackIso a b h c v hv)).hom).app U
        (tilde.toOpen (ModuleCat.of R (patchedModule a b h c)) U z) =
      tilde.toOpen (ModuleCat.of C C) (Spec.map (overlapMap a) ⁻¹ᵁ U) (a z.val.1) :=
  affineCompositeUnitIso_adjoint_toOpen (R := R) (A := A) (C := C)
    (CommRingCat.ofHom (algebraMap R A)) (CommRingCat.ofHom a) (overlapMap a) rfl
    (ModuleCat.of R (patchedModule a b h c)) (firstPullbackIso a b h c v hv)
    (fun z ↦ z.val.1) (firstPullbackIso_adjoint_toOpen a b h c v hv) U z


/-- On every open, the first overlap adjoint has the actual first-coordinate formula. -/
lemma firstOverlapIso_adjoint_toOpen (c : Cˣ) (v : Bˣ)
    (hv : Units.map b.toMonoidHom v = c) (U : (Spec R).Opens)
    (z : patchedModule a b h c) :
    (tildePullbackAdjoint (R := R) (A := C) (overlapMap a)
      (M := ModuleCat.of R (patchedModule a b h c))
      (N := SheafOfModules.unit (Spec C).ringCatSheaf)
      (firstOverlapIso a b h c v hv).hom).app U
        (tilde.toOpen (ModuleCat.of R (patchedModule a b h c)) U z) =
      tilde.toOpen (ModuleCat.of C C) (Spec.map (overlapMap a) ⁻¹ᵁ U) (a z.val.1) := by
  rw [firstOverlapIso_eq]
  exact firstOverlapComposite_adjoint_toOpen a b h c v hv U z


/-- On every open, the second overlap adjoint has the actual second-coordinate formula. -/
private lemma secondOverlapComposite_adjoint_toOpen (c : Cˣ) (v : Bˣ)
    (hv : Units.map b.toMonoidHom v = c) (U : (Spec R).Opens)
    (z : patchedModule a b h c) :
    (tildePullbackAdjoint (R := R) (A := C) (overlapMap a)
      (M := ModuleCat.of R (patchedModule a b h c))
      (N := SheafOfModules.unit (Spec C).ringCatSheaf) (affineCompositeUnitIso (R := R) (A := B) (C := C)
        (CommRingCat.ofHom (algebraMap R B)) (CommRingCat.ofHom b)
        (overlapMap a) h.w.symm (ModuleCat.of R (patchedModule a b h c))
        (secondPullbackIso a b h c v hv)).hom).app U
        (tilde.toOpen (ModuleCat.of R (patchedModule a b h c)) U z) =
      tilde.toOpen (ModuleCat.of C C) (Spec.map (overlapMap a) ⁻¹ᵁ U) (b z.val.2) :=
  affineCompositeUnitIso_adjoint_toOpen (R := R) (A := B) (C := C)
    (CommRingCat.ofHom (algebraMap R B)) (CommRingCat.ofHom b) (overlapMap a) h.w.symm
    (ModuleCat.of R (patchedModule a b h c)) (secondPullbackIso a b h c v hv)
    (fun z ↦ z.val.2) (secondPullbackIso_adjoint_toOpen a b h c v hv) U z


/-- On every open, the second overlap adjoint has the actual second-coordinate formula. -/
lemma secondOverlapIso_adjoint_toOpen (c : Cˣ) (v : Bˣ)
    (hv : Units.map b.toMonoidHom v = c) (U : (Spec R).Opens)
    (z : patchedModule a b h c) :
    (tildePullbackAdjoint (R := R) (A := C) (overlapMap a)
      (M := ModuleCat.of R (patchedModule a b h c))
      (N := SheafOfModules.unit (Spec C).ringCatSheaf)
      (secondOverlapIso a b h c v hv).hom).app U
        (tilde.toOpen (ModuleCat.of R (patchedModule a b h c)) U z) =
      tilde.toOpen (ModuleCat.of C C) (Spec.map (overlapMap a) ⁻¹ᵁ U) (b z.val.2) := by
  rw [secondOverlapIso_eq]
  exact secondOverlapComposite_adjoint_toOpen a b h c v hv U z


private lemma adjoint_comp_toOpen {S T : CommRingCat.{u}} (φ : S ⟶ T)
    {M : ModuleCat.{u} S} {N P : (Spec T).Modules}
    (g : (Scheme.Modules.pullback (Spec.map φ)).obj (tilde M) ⟶ N)
    (k : N ⟶ P) (U : (Spec S).Opens) (m : M) :
    (tildePullbackAdjoint (R := S) (A := T) φ (M := M) (N := P) (g ≫ k)).app U
        (tilde.toOpen M U m) =
      Scheme.Modules.Hom.app k (Spec.map φ ⁻¹ᵁ U)
        ((tildePullbackAdjoint (R := S) (A := T) φ (M := M) (N := N) g).app U
          (tilde.toOpen M U m)) := by
  dsimp only [tildePullbackAdjoint]
  rw [Adjunction.homEquiv_naturality_right]
  rfl

private lemma affine_transition {S T : CommRingCat.{u}} (φ : S ⟶ T)
    (M : ModuleCat.{u} S)
    (g₁ g₂ : (Scheme.Modules.pullback (Spec.map φ)).obj (tilde M) ⟶
      SheafOfModules.unit (Spec T).ringCatSheaf)
    (s : T) (q₁ q₂ : M → T)
    (h₁ : ∀ m, (tildePullbackAdjoint (R := S) (A := T) φ g₁).app ⊤
        (tilde.toOpen M ⊤ m) =
      tilde.toOpen (ModuleCat.of T T) (Spec.map φ ⁻¹ᵁ ⊤) (q₁ m))
    (h₂ : ∀ m, (tildePullbackAdjoint (R := S) (A := T) φ g₂).app ⊤
        (tilde.toOpen M ⊤ m) =
      tilde.toOpen (ModuleCat.of T T) (Spec.map φ ⁻¹ᵁ ⊤) (q₂ m))
    (hq : ∀ m, q₁ m = s * q₂ m) :
    g₁ = g₂ ≫ affineScalarHom (S := T) s := by
  apply tildePullback_hom_ext (R := S) (A := T) φ (M := M)
    (N := SheafOfModules.unit (Spec T).ringCatSheaf)
  intro m
  calc
    _ = tilde.toOpen (ModuleCat.of T T) (Spec.map φ ⁻¹ᵁ ⊤) (q₁ m) := h₁ m
    _ = tilde.toOpen (ModuleCat.of T T) (Spec.map φ ⁻¹ᵁ ⊤) (s * q₂ m) :=
      congrArg (tilde.toOpen (ModuleCat.of T T) _) (hq m)
    _ = Scheme.Modules.Hom.app (affineScalarHom (S := T) s) (Spec.map φ ⁻¹ᵁ ⊤)
        (tilde.toOpen (ModuleCat.of T T) (Spec.map φ ⁻¹ᵁ ⊤) (q₂ m)) :=
      (affineScalarHom_toOpen (S := T) s _ (q₂ m)).symm
    _ = Scheme.Modules.Hom.app (affineScalarHom (S := T) s) (Spec.map φ ⁻¹ᵁ ⊤)
        ((tildePullbackAdjoint (R := S) (A := T) φ g₂).app ⊤
          (tilde.toOpen M ⊤ m)) :=
      congrArg (Scheme.Modules.Hom.app (affineScalarHom (S := T) s) _) (h₂ m).symm
    _ = _ := (adjoint_comp_toOpen φ g₂ (affineScalarHom (S := T) s) ⊤ m).symm

private lemma adjoint_map_toOpen {S T : CommRingCat.{u}} (φ : S ⟶ T)
    {M M' : ModuleCat.{u} S} {N : (Spec T).Modules} (f : M ⟶ M')
    (g : (Scheme.Modules.pullback (Spec.map φ)).obj (tilde M') ⟶ N)
    (U : (Spec S).Opens) (m : M) :
    (tildePullbackAdjoint (R := S) (A := T) φ (M := M) (N := N)
      ((Scheme.Modules.pullback (Spec.map φ)).map (tilde.map f) ≫ g)).app U
        (tilde.toOpen M U m) =
      (tildePullbackAdjoint (R := S) (A := T) φ (M := M') (N := N) g).app U
        (tilde.toOpen M' U (f m)) := by
  dsimp only [tildePullbackAdjoint]
  rw [Adjunction.homEquiv_naturality_left]
  change (tildePullbackAdjoint (R := S) (A := T) φ (M := M') (N := N) g).app U
    ((tilde.map f).app U (tilde.toOpen M U m)) = _
  exact congrArg ((tildePullbackAdjoint (R := S) (A := T) φ
    (M := M') (N := N) g).app U) (ConcreteCategory.congr_hom (tilde.toOpen_map_app f U) m)

private lemma affine_diagonal_naturality {S T : CommRingCat.{u}} (φ : S ⟶ T)
    (M M' : ModuleCat.{u} S) (f : M ⟶ M')
    (g : (Scheme.Modules.pullback (Spec.map φ)).obj (tilde M) ⟶
      SheafOfModules.unit (Spec T).ringCatSheaf)
    (g' : (Scheme.Modules.pullback (Spec.map φ)).obj (tilde M') ⟶
      SheafOfModules.unit (Spec T).ringCatSheaf)
    (s : T) (q : M → T) (q' : M' → T)
    (hg : ∀ m, (tildePullbackAdjoint (R := S) (A := T) φ g).app ⊤
        (tilde.toOpen M ⊤ m) =
      tilde.toOpen (ModuleCat.of T T) (Spec.map φ ⁻¹ᵁ ⊤) (q m))
    (hg' : ∀ m, (tildePullbackAdjoint (R := S) (A := T) φ g').app ⊤
        (tilde.toOpen M' ⊤ m) =
      tilde.toOpen (ModuleCat.of T T) (Spec.map φ ⁻¹ᵁ ⊤) (q' m))
    (hq : ∀ m, q' (f m) = s * q m) :
    (Scheme.Modules.pullback (Spec.map φ)).map (tilde.map f) ≫ g' =
      g ≫ affineScalarHom (S := T) s :=
  affine_transition φ M _ g s (fun m ↦ q' (f m)) q
    (fun m ↦ (adjoint_map_toOpen φ f g' ⊤ m).trans (hg' (f m))) hg hq

/-- The prescribed unit is the actual transition morphism on the ordinary common pullback. -/
lemma overlap_identity (c : Cˣ) (v : Bˣ) (hv : Units.map b.toMonoidHom v = c) :
    (firstOverlapIso a b h c v hv).hom =
      (secondOverlapIso a b h c v hv).hom ≫ affineScalarHom (S := C) (c : C) :=
  affine_transition (S := R) (T := C) (overlapMap a)
    (ModuleCat.of R (patchedModule a b h c))
    (firstOverlapIso a b h c v hv).hom (secondOverlapIso a b h c v hv).hom
    (c : C) (fun z ↦ a z.val.1) (fun z ↦ b z.val.2)
    (firstOverlapIso_adjoint_toOpen a b h c v hv ⊤)
    (secondOverlapIso_adjoint_toOpen a b h c v hv ⊤) (fun z ↦ z.property)

/-- The first overlap isomorphism does not depend on the chosen unit lift. -/
lemma firstOverlapIso_independent (c : Cˣ) (v w : Bˣ)
    (hv : Units.map b.toMonoidHom v = c) (hw : Units.map b.toMonoidHom w = c) :
    firstOverlapIso a b h c v hv = firstOverlapIso a b h c w hw := by
  simp only [firstOverlapIso_eq]
  rw [firstPullbackIso_independent a b h c v w hv hw]

/-- The second overlap isomorphism does not depend on the chosen unit lift. -/
lemma secondOverlapIso_independent (c : Cˣ) (v w : Bˣ)
    (hv : Units.map b.toMonoidHom v = c) (hw : Units.map b.toMonoidHom w = c) :
    secondOverlapIso a b h c v hv = secondOverlapIso a b h c w hw := by
  simp only [secondOverlapIso_eq]
  rw [secondPullbackIso_independent a b h c v w hv hw]

/-- The first common-overlap isomorphism preserves the prescribed first diagonal coefficient. -/
lemma firstOverlapIso_diagonalSheafMap (c d : Cˣ) (v w : Bˣ)
    (hv : Units.map b.toMonoidHom v = c) (hw : Units.map b.toMonoidHom w = d)
    (x : A) (y : B) (hxy : a x * (c : C) = (d : C) * b y) :
    (Scheme.Modules.pullback (Spec.map (overlapMap a))).map
        (diagonalSheafMap a b h c d x y hxy) ≫ (firstOverlapIso a b h d w hw).hom =
      (firstOverlapIso a b h c v hv).hom ≫ affineScalarHom (S := C) (a x) :=
  affine_diagonal_naturality (S := R) (T := C) (overlapMap a)
    (ModuleCat.of R (patchedModule a b h c)) (ModuleCat.of R (patchedModule a b h d))
    (ModuleCat.ofHom (diagonalMap a b h c d x y hxy))
    (firstOverlapIso a b h c v hv).hom (firstOverlapIso a b h d w hw).hom
    (a x) (fun z ↦ a z.val.1) (fun z ↦ a z.val.1)
    (firstOverlapIso_adjoint_toOpen a b h c v hv ⊤)
    (firstOverlapIso_adjoint_toOpen a b h d w hw ⊤) (fun z ↦ map_mul a x z.val.1)

/-- The second common-overlap isomorphism preserves the prescribed second diagonal coefficient. -/
lemma secondOverlapIso_diagonalSheafMap (c d : Cˣ) (v w : Bˣ)
    (hv : Units.map b.toMonoidHom v = c) (hw : Units.map b.toMonoidHom w = d)
    (x : A) (y : B) (hxy : a x * (c : C) = (d : C) * b y) :
    (Scheme.Modules.pullback (Spec.map (overlapMap a))).map
        (diagonalSheafMap a b h c d x y hxy) ≫ (secondOverlapIso a b h d w hw).hom =
      (secondOverlapIso a b h c v hv).hom ≫ affineScalarHom (S := C) (b y) :=
  affine_diagonal_naturality (S := R) (T := C) (overlapMap a)
    (ModuleCat.of R (patchedModule a b h c)) (ModuleCat.of R (patchedModule a b h d))
    (ModuleCat.ofHom (diagonalMap a b h c d x y hxy))
    (secondOverlapIso a b h c v hv).hom (secondOverlapIso a b h d w hw).hom
    (b y) (fun z ↦ b z.val.2) (fun z ↦ b z.val.2)
    (secondOverlapIso_adjoint_toOpen a b h c v hv ⊤)
    (secondOverlapIso_adjoint_toOpen a b h d w hw ⊤) (fun z ↦ map_mul b y z.val.2)

/-- The first overlap trivialization retains the first prescribed unit of a diagonal isomorphism. -/
lemma firstOverlapIso_diagonalSheafIso (c d : Cˣ) (v w : Bˣ)
    (hv : Units.map b.toMonoidHom v = c) (hw : Units.map b.toMonoidHom w = d)
    (x : Aˣ) (y : Bˣ)
    (hxy : Units.map a.toMonoidHom x * c = d * Units.map b.toMonoidHom y) :
    (Scheme.Modules.pullback (Spec.map (overlapMap a))).map
        (diagonalSheafIso a b h c d x y hxy).hom ≫ (firstOverlapIso a b h d w hw).hom =
      (firstOverlapIso a b h c v hv).hom ≫ affineScalarHom (S := C) (a (x : A)) :=
  firstOverlapIso_diagonalSheafMap a b h c d v w hv hw (x : A) (y : B)
    (congrArg Units.val hxy)

/-- The second overlap trivialization retains the second prescribed unit of a diagonal isomorphism. -/
lemma secondOverlapIso_diagonalSheafIso (c d : Cˣ) (v w : Bˣ)
    (hv : Units.map b.toMonoidHom v = c) (hw : Units.map b.toMonoidHom w = d)
    (x : Aˣ) (y : Bˣ)
    (hxy : Units.map a.toMonoidHom x * c = d * Units.map b.toMonoidHom y) :
    (Scheme.Modules.pullback (Spec.map (overlapMap a))).map
        (diagonalSheafIso a b h c d x y hxy).hom ≫ (secondOverlapIso a b h d w hw).hom =
      (secondOverlapIso a b h c v hv).hom ≫ affineScalarHom (S := C) (b (y : B)) :=
  secondOverlapIso_diagonalSheafMap a b h c d v w hv hw (x : A) (y : B)
    (congrArg Units.val hxy)

/-- A surjective nilpotent leg gives the actual line bundle with coherent ordinary trivializations. -/
lemma exists_lineBundle_and_coherent_pullbackIsos (hb : Function.Surjective b)
    (hker : IsNilpotent (RingHom.ker b)) (c : Cˣ) :
    IsLocallyFreeRankOne (patchedSheaf a b h c) ∧
      ∃ eA : (Scheme.Modules.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R A)))).obj (patchedSheaf a b h c) ≅
          SheafOfModules.unit (Spec A).ringCatSheaf,
      ∃ eB : (Scheme.Modules.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R B)))).obj (patchedSheaf a b h c) ≅
          SheafOfModules.unit (Spec B).ringCatSheaf,
      (∀ U z, (tildePullbackAdjoint (R := R) (A := A)
          (CommRingCat.ofHom (algebraMap R A)) eA.hom).app U
        (tilde.toOpen (ModuleCat.of R (patchedModule a b h c)) U z) =
          tilde.toOpen (ModuleCat.of A A)
            (Spec.map (CommRingCat.ofHom (algebraMap R A)) ⁻¹ᵁ U) z.val.1) ∧
      (∀ U z, (tildePullbackAdjoint (R := R) (A := B)
          (CommRingCat.ofHom (algebraMap R B)) eB.hom).app U
        (tilde.toOpen (ModuleCat.of R (patchedModule a b h c)) U z) =
          tilde.toOpen (ModuleCat.of B B)
            (Spec.map (CommRingCat.ofHom (algebraMap R B)) ⁻¹ᵁ U) z.val.2) ∧
      (∀ U z, (tildePullbackAdjoint (R := R) (A := C) (overlapMap a)
          (affineCompositeUnitIso (R := R) (A := A) (C := C)
            (CommRingCat.ofHom (algebraMap R A)) (CommRingCat.ofHom a)
            (overlapMap a) rfl (ModuleCat.of R (patchedModule a b h c)) eA).hom).app U
        (tilde.toOpen (ModuleCat.of R (patchedModule a b h c)) U z) =
          tilde.toOpen (ModuleCat.of C C) (Spec.map (overlapMap a) ⁻¹ᵁ U) (a z.val.1)) ∧
      (∀ U z, (tildePullbackAdjoint (R := R) (A := C) (overlapMap a)
          (affineCompositeUnitIso (R := R) (A := B) (C := C)
            (CommRingCat.ofHom (algebraMap R B)) (CommRingCat.ofHom b)
            (overlapMap a) h.w.symm (ModuleCat.of R (patchedModule a b h c)) eB).hom).app U
        (tilde.toOpen (ModuleCat.of R (patchedModule a b h c)) U z) =
          tilde.toOpen (ModuleCat.of C C) (Spec.map (overlapMap a) ⁻¹ᵁ U) (b z.val.2)) ∧
      (affineCompositeUnitIso (R := R) (A := A) (C := C)
          (CommRingCat.ofHom (algebraMap R A)) (CommRingCat.ofHom a)
          (overlapMap a) rfl (ModuleCat.of R (patchedModule a b h c)) eA).hom =
        (affineCompositeUnitIso (R := R) (A := B) (C := C)
          (CommRingCat.ofHom (algebraMap R B)) (CommRingCat.ofHom b)
          (overlapMap a) h.w.symm (ModuleCat.of R (patchedModule a b h c)) eB).hom ≫
            affineScalarHom (S := C) (c : C) := by
  obtain ⟨hP, eA, eB, hA, hB⟩ := exists_lineBundle_and_pullbackIsos a b h hb hker c
  have hAC := affineCompositeUnitIso_adjoint_toOpen (R := R) (A := A) (C := C)
    (CommRingCat.ofHom (algebraMap R A)) (CommRingCat.ofHom a)
    (overlapMap a) rfl (ModuleCat.of R (patchedModule a b h c)) eA (fun z ↦ z.val.1) hA
  have hBC := affineCompositeUnitIso_adjoint_toOpen (R := R) (A := B) (C := C)
    (CommRingCat.ofHom (algebraMap R B)) (CommRingCat.ofHom b)
    (overlapMap a) h.w.symm (ModuleCat.of R (patchedModule a b h c)) eB (fun z ↦ z.val.2) hB
  refine ⟨hP, eA, eB, hA, hB, hAC, hBC, ?_⟩
  exact affine_transition (S := R) (T := C) (overlapMap a)
    (ModuleCat.of R (patchedModule a b h c)) _ _
    (c : C) (fun z ↦ a z.val.1) (fun z ↦ b z.val.2) (hAC ⊤) (hBC ⊤) (fun z ↦ z.property)


end Langlands.AlgebraicGeometry.Picard.InfinitesimalRankOneSheafOverlap
