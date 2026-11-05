import Langlands.AlgebraicGeometry.Picard.InfinitesimalRankOnePatching
import Langlands.AlgebraicGeometry.Picard.LineBundlePullback
import Langlands.AlgebraicGeometry.Modules.TildePullback
import Langlands.AlgebraicGeometry.Modules.PullbackUnitProofs
import Mathlib.Algebra.Module.Equiv.Basic

/-! # Associated sheaves of patched free rank-one modules -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard.InfinitesimalRankOneSheaf

open InfinitesimalRankOnePatching
open Langlands.Scheme.Modules

variable {R A B C : CommRingCat.{u}} [Algebra R A] [Algebra R B]
  (a : A →+* C) (b : B →+* C)
  (h : IsPullback (CommRingCat.ofHom (algebraMap R A))
    (CommRingCat.ofHom (algebraMap R B)) (CommRingCat.ofHom a) (CommRingCat.ofHom b))

/-- The actual associated sheaf of the prescribed compatible-pair module. -/
def patchedSheaf (c : Cˣ) : (Spec R).Modules :=
  tilde (ModuleCat.of R (patchedModule a b h c))

/-- The published module frame induces an actual global sheaf trivialization. -/
def frameIso (c : Cˣ) (v : Bˣ) (hv : Units.map b.toMonoidHom v = c) :
    patchedSheaf a b h c ≅ SheafOfModules.unit (Spec R).ringCatSheaf :=
  (tilde.functor R).mapIso (frameEquiv a b h c v hv).symm.toModuleIso ≪≫ tildeSelf

/-- The associated sheaf is an actual line bundle, with its inherited sheaf object. -/
def patchedLineBundle (c : Cˣ) (v : Bˣ) (hv : Units.map b.toMonoidHom v = c) :
    LineBundle (Spec R) :=
  LineBundle.ofIso (LineBundle.trivial (Spec R)) (frameIso a b h c v hv).symm

/-- Ordinary pullback of the chosen global frame along an affine morphism. -/
def framePullbackIso {S : CommRingCat.{u}} (φ : R ⟶ S)
    (c : Cˣ) (v : Bˣ) (hv : Units.map b.toMonoidHom v = c) :
    (Scheme.Modules.pullback (Spec.map φ)).obj (patchedSheaf a b h c) ≅
        SheafOfModules.unit (Spec S).ringCatSheaf :=
  (Scheme.Modules.pullback _).mapIso (frameIso a b h c v hv) ≪≫ pullbackUnitIso _

/-- Multiplication by the inverse unit on the actual structure sheaf. -/
def inverseUnitIso (v : Bˣ) :
    SheafOfModules.unit (Spec B).ringCatSheaf ≅
      SheafOfModules.unit (Spec B).ringCatSheaf :=
  tildeSelf.symm ≪≫
    (tilde.functor B).mapIso (v⁻¹.mulLeftLinearEquiv B B).toModuleIso ≪≫ tildeSelf

/-- The first ordinary pullback trivialization, obtained from the global frame. -/
def firstPullbackIso (c : Cˣ) (v : Bˣ) (hv : Units.map b.toMonoidHom v = c) :
    (Scheme.Modules.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))).obj (patchedSheaf a b h c) ≅
        SheafOfModules.unit (Spec A).ringCatSheaf :=
  framePullbackIso a b h (CommRingCat.ofHom (algebraMap R A)) c v hv

/-- The second ordinary pullback uses the second coordinate of the published frame. -/
def secondPullbackIso (c : Cˣ) (v : Bˣ) (hv : Units.map b.toMonoidHom v = c) :
    (Scheme.Modules.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap R B)))).obj (patchedSheaf a b h c) ≅
        SheafOfModules.unit (Spec B).ringCatSheaf :=
  framePullbackIso a b h (CommRingCat.ofHom (algebraMap R B)) c v hv ≪≫ inverseUnitIso v

private lemma unitToPushforwardUnit_toOpen {S T : CommRingCat.{u}} (φ : S ⟶ T)
    (U : (Spec S).Opens) (r : S) :
    Scheme.Modules.Hom.app (unitToPushforwardUnit (Spec.map φ)) U
      (tilde.toOpen (ModuleCat.of S S) U r) =
    tilde.toOpen (ModuleCat.of T T) (Spec.map φ ⁻¹ᵁ U) (φ r) := by
  exact ConcreteCategory.congr_hom (StructureSheaf.toOpen_comp_comap φ.hom U) r

/-- The frame map evaluates every associated-sheaf generator by the inverse module frame. -/
lemma frameIso_toOpen (c : Cˣ) (v : Bˣ) (hv : Units.map b.toMonoidHom v = c)
    (U : (Spec R).Opens) (z : patchedModule a b h c) :
    (frameIso a b h c v hv).hom.app U
        (tilde.toOpen (ModuleCat.of R (patchedModule a b h c)) U z) =
      tilde.toOpen (ModuleCat.of R R) U ((frameEquiv a b h c v hv).symm z) := by
  exact ConcreteCategory.congr_hom
    (tilde.toOpen_map_app (frameEquiv a b h c v hv).symm.toModuleIso.hom U) z

/-- The ordinary pulled-back frame has the expected adjoint on every generator. -/
lemma framePullbackIso_adjoint_toOpen {S : CommRingCat.{u}} (φ : R ⟶ S)
    (c : Cˣ) (v : Bˣ) (hv : Units.map b.toMonoidHom v = c)
    (U : (Spec R).Opens) (z : patchedModule a b h c) :
    (tildePullbackAdjoint φ (framePullbackIso a b h φ c v hv).hom).app U
        (tilde.toOpen (ModuleCat.of R (patchedModule a b h c)) U z) =
      tilde.toOpen (ModuleCat.of S S) (Spec.map φ ⁻¹ᵁ U)
        (φ ((frameEquiv a b h c v hv).symm z)) := by
  dsimp only [framePullbackIso, Iso.trans_hom, Functor.mapIso_hom, tildePullbackAdjoint]
  rw [Adjunction.homEquiv_naturality_left, pullbackUnitAdjunction]
  change Scheme.Modules.Hom.app (unitToPushforwardUnit (Spec.map φ)) U
    ((frameIso a b h c v hv).hom.app U
      (tilde.toOpen (ModuleCat.of R (patchedModule a b h c)) U z)) = _
  rw [frameIso_toOpen, unitToPushforwardUnit_toOpen]

private lemma inverseUnitIso_toOpen (v : Bˣ) (U : (Spec B).Opens) (r : B) :
    Scheme.Modules.Hom.app (inverseUnitIso v).hom U (tilde.toOpen (ModuleCat.of B B) U r) =
      tilde.toOpen (ModuleCat.of B B) U ((↑v⁻¹ : B) * r) := by
  exact ConcreteCategory.congr_hom
    (tilde.toOpen_map_app (v⁻¹.mulLeftLinearEquiv B B).toModuleIso.hom U) r

/-- On every open, the adjoint of the first trivialization is the actual first projection. -/
lemma firstPullbackIso_adjoint_toOpen (c : Cˣ) (v : Bˣ)
    (hv : Units.map b.toMonoidHom v = c) (U : (Spec R).Opens)
    (z : patchedModule a b h c) :
    (tildePullbackAdjoint (CommRingCat.ofHom (algebraMap R A))
      (firstPullbackIso a b h c v hv).hom).app U
        (tilde.toOpen (ModuleCat.of R (patchedModule a b h c)) U z) =
      tilde.toOpen (ModuleCat.of A A)
        (Spec.map (CommRingCat.ofHom (algebraMap R A)) ⁻¹ᵁ U) z.val.1 := by
  have hp := congrArg (fun w : patchedModule a b h c ↦ w.val.1)
    ((frameEquiv a b h c v hv).apply_symm_apply z)
  change algebraMap R A ((frameEquiv a b h c v hv).symm z) = z.val.1 at hp
  change (tildePullbackAdjoint (CommRingCat.ofHom (algebraMap R A))
    (framePullbackIso a b h (S := A) (CommRingCat.ofHom (algebraMap R A)) c v hv).hom).app U _ = _
  exact (framePullbackIso_adjoint_toOpen a b h (S := A)
    (CommRingCat.ofHom (algebraMap R A)) c v hv U z).trans
      (congrArg (tilde.toOpen (ModuleCat.of A A) _) hp)

/-- On every open, the adjoint of the second trivialization is the actual second projection. -/
lemma secondPullbackIso_adjoint_toOpen (c : Cˣ) (v : Bˣ)
    (hv : Units.map b.toMonoidHom v = c) (U : (Spec R).Opens)
    (z : patchedModule a b h c) :
    (tildePullbackAdjoint (CommRingCat.ofHom (algebraMap R B))
      (secondPullbackIso a b h c v hv).hom).app U
        (tilde.toOpen (ModuleCat.of R (patchedModule a b h c)) U z) =
      tilde.toOpen (ModuleCat.of B B)
        (Spec.map (CommRingCat.ofHom (algebraMap R B)) ⁻¹ᵁ U) z.val.2 := by
  have hq := congrArg (fun w : patchedModule a b h c ↦ w.val.2)
    ((frameEquiv a b h c v hv).apply_symm_apply z)
  change (↑v⁻¹ : B) * algebraMap R B ((frameEquiv a b h c v hv).symm z) = z.val.2 at hq
  rw [secondPullbackIso, Iso.trans_hom, tildePullbackAdjoint,
    Adjunction.homEquiv_naturality_right]
  change Scheme.Modules.Hom.app (inverseUnitIso v).hom
    (Spec.map (CommRingCat.ofHom (algebraMap R B)) ⁻¹ᵁ U)
      ((tildePullbackAdjoint (CommRingCat.ofHom (algebraMap R B))
        (framePullbackIso a b h (CommRingCat.ofHom (algebraMap R B)) c v hv).hom).app U
          (tilde.toOpen (ModuleCat.of R (patchedModule a b h c)) U z)) = _
  rw [framePullbackIso_adjoint_toOpen, inverseUnitIso_toOpen]
  exact congrArg (tilde.toOpen (ModuleCat.of B B) _) hq

/-- The adjoint first-projection formula uniquely determines the ordinary pullback isomorphism. -/
lemma firstPullbackIso_unique (c : Cˣ) (v : Bˣ)
    (hv : Units.map b.toMonoidHom v = c)
    (e : (Scheme.Modules.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))).obj (patchedSheaf a b h c) ≅
        SheafOfModules.unit (Spec A).ringCatSheaf)
    (he : ∀ z : patchedModule a b h c,
      (tildePullbackAdjoint (CommRingCat.ofHom (algebraMap R A)) e.hom).app ⊤
        (tilde.toOpen (ModuleCat.of R (patchedModule a b h c)) ⊤ z) =
      tilde.toOpen (ModuleCat.of A A)
        (Spec.map (CommRingCat.ofHom (algebraMap R A)) ⁻¹ᵁ ⊤) z.val.1) :
    e = firstPullbackIso a b h c v hv := by
  apply Iso.ext
  apply tildePullback_hom_ext (CommRingCat.ofHom (algebraMap R A))
    (M := ModuleCat.of R (patchedModule a b h c))
  intro z
  exact (he z).trans (firstPullbackIso_adjoint_toOpen a b h c v hv ⊤ z).symm

/-- The adjoint second-projection formula uniquely determines the ordinary pullback isomorphism. -/
lemma secondPullbackIso_unique (c : Cˣ) (v : Bˣ)
    (hv : Units.map b.toMonoidHom v = c)
    (e : (Scheme.Modules.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap R B)))).obj (patchedSheaf a b h c) ≅
        SheafOfModules.unit (Spec B).ringCatSheaf)
    (he : ∀ z : patchedModule a b h c,
      (tildePullbackAdjoint (CommRingCat.ofHom (algebraMap R B)) e.hom).app ⊤
        (tilde.toOpen (ModuleCat.of R (patchedModule a b h c)) ⊤ z) =
      tilde.toOpen (ModuleCat.of B B)
        (Spec.map (CommRingCat.ofHom (algebraMap R B)) ⁻¹ᵁ ⊤) z.val.2) :
    e = secondPullbackIso a b h c v hv := by
  apply Iso.ext
  apply tildePullback_hom_ext (CommRingCat.ofHom (algebraMap R B))
    (M := ModuleCat.of R (patchedModule a b h c))
  intro z
  exact (he z).trans (secondPullbackIso_adjoint_toOpen a b h c v hv ⊤ z).symm

/-- The first ordinary pullback isomorphism is independent of the chosen unit lift. -/
lemma firstPullbackIso_independent (c : Cˣ) (v w : Bˣ)
    (hv : Units.map b.toMonoidHom v = c) (hw : Units.map b.toMonoidHom w = c) :
    firstPullbackIso a b h c v hv = firstPullbackIso a b h c w hw :=
  firstPullbackIso_unique a b h c w hw _ (firstPullbackIso_adjoint_toOpen a b h c v hv ⊤)

/-- The second ordinary pullback isomorphism is independent of the chosen unit lift. -/
lemma secondPullbackIso_independent (c : Cˣ) (v w : Bˣ)
    (hv : Units.map b.toMonoidHom v = c) (hw : Units.map b.toMonoidHom w = c) :
    secondPullbackIso a b h c v hv = secondPullbackIso a b h c w hw :=
  secondPullbackIso_unique a b h c w hw _ (secondPullbackIso_adjoint_toOpen a b h c v hv ⊤)

/-- Compatible diagonal maps induce morphisms of the actual associated sheaves. -/
def diagonalSheafMap (c d : Cˣ) (x : A) (y : B)
    (hxy : a x * (c : C) = (d : C) * b y) :
    patchedSheaf a b h c ⟶ patchedSheaf a b h d :=
  tilde.map (ModuleCat.ofHom (diagonalMap a b h c d x y hxy))

/-- Compatible diagonal units induce actual associated-sheaf isomorphisms. -/
def diagonalSheafIso (c d : Cˣ) (x : Aˣ) (y : Bˣ)
    (hxy : Units.map a.toMonoidHom x * c = d * Units.map b.toMonoidHom y) :
    patchedSheaf a b h c ≅ patchedSheaf a b h d :=
  (tilde.functor R).mapIso (diagonalEquiv a b h c d x y hxy).toModuleIso

/-- On every open, the actual diagonal sheaf map retains the prescribed pair map. -/
lemma diagonalSheafMap_toOpen (c d : Cˣ) (x : A) (y : B)
    (hxy : a x * (c : C) = (d : C) * b y)
    (U : (Spec R).Opens) (z : patchedModule a b h c) :
    (diagonalSheafMap a b h c d x y hxy).app U
        (tilde.toOpen (ModuleCat.of R (patchedModule a b h c)) U z) =
      tilde.toOpen (ModuleCat.of R (patchedModule a b h d)) U
        (diagonalMap a b h c d x y hxy z) := by
  exact ConcreteCategory.congr_hom
    (tilde.toOpen_map_app (ModuleCat.ofHom (diagonalMap a b h c d x y hxy)) U) z

/-- On an affine scheme, multiplication by the specified ring element as a sheaf morphism. -/
def affineScalarHom {S : CommRingCat.{u}} (s : S) :
    SheafOfModules.unit (Spec S).ringCatSheaf ⟶
      SheafOfModules.unit (Spec S).ringCatSheaf :=
  tildeSelf.inv ≫ tilde.map (ModuleCat.ofHom (LinearMap.mulLeft S s)) ≫ tildeSelf.hom

/-- The scalar sheaf morphism multiplies associated-sheaf generators by its specified scalar. -/
lemma affineScalarHom_toOpen {S : CommRingCat.{u}} (s : S)
    (U : (Spec S).Opens) (r : S) :
    Scheme.Modules.Hom.app (affineScalarHom s) U (tilde.toOpen (ModuleCat.of S S) U r) =
      tilde.toOpen (ModuleCat.of S S) U (s * r) := by
  exact ConcreteCategory.congr_hom
    (tilde.toOpen_map_app (ModuleCat.ofHom (LinearMap.mulLeft S s)) U) r

/-- The first trivialization intertwines the prescribed diagonal sheaf map and its first scalar. -/
lemma firstPullbackIso_diagonalSheafMap (c d : Cˣ) (v w : Bˣ)
    (hv : Units.map b.toMonoidHom v = c) (hw : Units.map b.toMonoidHom w = d)
    (x : A) (y : B) (hxy : a x * (c : C) = (d : C) * b y) :
    (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap R A)))).map
        (diagonalSheafMap a b h c d x y hxy) ≫ (firstPullbackIso a b h d w hw).hom =
      (firstPullbackIso a b h c v hv).hom ≫ affineScalarHom x := by
  apply tildePullback_hom_ext (CommRingCat.ofHom (algebraMap R A))
    (M := ModuleCat.of R (patchedModule a b h c))
  intro z
  dsimp only [tildePullbackAdjoint]
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  change (tildePullbackAdjoint (CommRingCat.ofHom (algebraMap R A))
      (firstPullbackIso a b h d w hw).hom).app ⊤
        ((diagonalSheafMap a b h c d x y hxy).app ⊤
          (tilde.toOpen (ModuleCat.of R (patchedModule a b h c)) ⊤ z)) =
    Scheme.Modules.Hom.app (affineScalarHom x)
      (Spec.map (CommRingCat.ofHom (algebraMap R A)) ⁻¹ᵁ ⊤)
        ((tildePullbackAdjoint (CommRingCat.ofHom (algebraMap R A))
          (firstPullbackIso a b h c v hv).hom).app ⊤
            (tilde.toOpen (ModuleCat.of R (patchedModule a b h c)) ⊤ z))
  rw [diagonalSheafMap_toOpen, firstPullbackIso_adjoint_toOpen,
    firstPullbackIso_adjoint_toOpen, affineScalarHom_toOpen]
  rfl

/-- The second trivialization intertwines the prescribed diagonal sheaf map and its second scalar. -/
lemma secondPullbackIso_diagonalSheafMap (c d : Cˣ) (v w : Bˣ)
    (hv : Units.map b.toMonoidHom v = c) (hw : Units.map b.toMonoidHom w = d)
    (x : A) (y : B) (hxy : a x * (c : C) = (d : C) * b y) :
    (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))).map
        (diagonalSheafMap a b h c d x y hxy) ≫ (secondPullbackIso a b h d w hw).hom =
      (secondPullbackIso a b h c v hv).hom ≫ affineScalarHom y := by
  apply tildePullback_hom_ext (CommRingCat.ofHom (algebraMap R B))
    (M := ModuleCat.of R (patchedModule a b h c))
  intro z
  dsimp only [tildePullbackAdjoint]
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  change (tildePullbackAdjoint (CommRingCat.ofHom (algebraMap R B))
      (secondPullbackIso a b h d w hw).hom).app ⊤
        ((diagonalSheafMap a b h c d x y hxy).app ⊤
          (tilde.toOpen (ModuleCat.of R (patchedModule a b h c)) ⊤ z)) =
    Scheme.Modules.Hom.app (affineScalarHom y)
      (Spec.map (CommRingCat.ofHom (algebraMap R B)) ⁻¹ᵁ ⊤)
        ((tildePullbackAdjoint (CommRingCat.ofHom (algebraMap R B))
          (secondPullbackIso a b h c v hv).hom).app ⊤
            (tilde.toOpen (ModuleCat.of R (patchedModule a b h c)) ⊤ z))
  rw [diagonalSheafMap_toOpen, secondPullbackIso_adjoint_toOpen,
    secondPullbackIso_adjoint_toOpen, affineScalarHom_toOpen]
  rfl

/-- The first trivialization retains the first prescribed unit in an actual sheaf isomorphism. -/
lemma firstPullbackIso_diagonalSheafIso (c d : Cˣ) (v w : Bˣ)
    (hv : Units.map b.toMonoidHom v = c) (hw : Units.map b.toMonoidHom w = d)
    (x : Aˣ) (y : Bˣ)
    (hxy : Units.map a.toMonoidHom x * c = d * Units.map b.toMonoidHom y) :
    (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap R A)))).map
        (diagonalSheafIso a b h c d x y hxy).hom ≫ (firstPullbackIso a b h d w hw).hom =
      (firstPullbackIso a b h c v hv).hom ≫ affineScalarHom (x : A) :=
  firstPullbackIso_diagonalSheafMap a b h c d v w hv hw (x : A) (y : B)
    (congrArg Units.val hxy)

/-- The second trivialization retains the second prescribed unit in an actual sheaf isomorphism. -/
lemma secondPullbackIso_diagonalSheafIso (c d : Cˣ) (v w : Bˣ)
    (hv : Units.map b.toMonoidHom v = c) (hw : Units.map b.toMonoidHom w = d)
    (x : Aˣ) (y : Bˣ)
    (hxy : Units.map a.toMonoidHom x * c = d * Units.map b.toMonoidHom y) :
    (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))).map
        (diagonalSheafIso a b h c d x y hxy).hom ≫ (secondPullbackIso a b h d w hw).hom =
      (secondPullbackIso a b h c v hv).hom ≫ affineScalarHom (y : B) :=
  secondPullbackIso_diagonalSheafMap a b h c d v w hv hw (x : A) (y : B)
    (congrArg Units.val hxy)

/-- A surjective nilpotent leg supplies the actual line bundle and both projection isomorphisms. -/
lemma exists_lineBundle_and_pullbackIsos (hb : Function.Surjective b)
    (hker : IsNilpotent (RingHom.ker b)) (c : Cˣ) :
    IsLocallyFreeRankOne (patchedSheaf a b h c) ∧
      ∃ eA : (Scheme.Modules.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R A)))).obj (patchedSheaf a b h c) ≅
          SheafOfModules.unit (Spec A).ringCatSheaf,
      ∃ eB : (Scheme.Modules.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R B)))).obj (patchedSheaf a b h c) ≅
          SheafOfModules.unit (Spec B).ringCatSheaf,
      (∀ U z, (tildePullbackAdjoint (CommRingCat.ofHom (algebraMap R A)) eA.hom).app U
        (tilde.toOpen (ModuleCat.of R (patchedModule a b h c)) U z) =
          tilde.toOpen (ModuleCat.of A A)
            (Spec.map (CommRingCat.ofHom (algebraMap R A)) ⁻¹ᵁ U) z.val.1) ∧
      ∀ U z, (tildePullbackAdjoint (CommRingCat.ofHom (algebraMap R B)) eB.hom).app U
        (tilde.toOpen (ModuleCat.of R (patchedModule a b h c)) U z) =
          tilde.toOpen (ModuleCat.of B B)
            (Spec.map (CommRingCat.ofHom (algebraMap R B)) ⁻¹ᵁ U) z.val.2 := by
  obtain ⟨v, hv⟩ := NilpotentUnitReduction.unitsMap_surjective b hb hker c
  exact ⟨(patchedLineBundle a b h c v hv).property, firstPullbackIso a b h c v hv,
    secondPullbackIso a b h c v hv, firstPullbackIso_adjoint_toOpen a b h c v hv,
    secondPullbackIso_adjoint_toOpen a b h c v hv⟩

end Langlands.AlgebraicGeometry.Picard.InfinitesimalRankOneSheaf
