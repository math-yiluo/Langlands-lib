import Langlands.AlgebraicGeometry.LocalSectionBasis
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Free sheaf frames from bases on affine subopens -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry Opposite

namespace Langlands.Scheme.Modules

section Free

variable {X : Scheme.{u}} (U : X.Opens) (I : Type u) [Fintype I]

local instance affineBasisFrameIndexDecidableEq : DecidableEq I := Classical.decEq I

omit [Fintype I] in
private theorem freeCoordinate_freeSection (i j : I) (W : Over U) :
    (freeCoordinate U I i).val.app (op W)
        ((SheafOfModules.freeSection j).val (op W)) =
      if j = i then (1 : Γ(X, W.left)) else 0 := by
  have hh := congrArg (fun f => f.val.app (op W) (1 : Γ(X, W.left)))
    (ιFree_freeCoordinate (X := X) (U := U) i j)
  by_cases hji : j = i
  · rw [ite_eq_left hji] at hh ⊢
    exact hh
  · rw [ite_eq_right hji] at hh ⊢
    exact hh

omit [Fintype I] in
private theorem sum_app {A B : SheafOfModules (X.ringCatSheaf.over U)}
    (s : Finset I) (f : I → (A ⟶ B)) (W : (Over U)ᵒᵖ) (x : A.val.obj W) :
    (∑ j ∈ s, f j).val.app W x = ∑ j ∈ s, (f j).val.app W x := by
  induction s using Finset.induction_on with
  | empty => rfl
  | @insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    change (f j).val.app W x + (∑ j ∈ s, f j).val.app W x = _
    rw [ih]

private theorem free_expansion (W : Over U)
    (x : (SheafOfModules.free (R := X.ringCatSheaf.over U) I).val.obj (op W)) :
    ∑ i, (show Γ(X, W.left) from (freeCoordinate U I i).val.app (op W) x) •
      (show (SheafOfModules.free (R := X.ringCatSheaf.over U) I).val.obj (op W)
        from (SheafOfModules.freeSection i).val (op W)) = x := by
  have hh := congrArg (fun f => f.val.app (op W) x)
    (freeCoordinate_total (X := X) (U := U) (I := I))
  rw [sum_app] at hh
  change (∑ i : I, (SheafOfModules.ιFree i).val.app (op W)
    ((freeCoordinate U I i).val.app (op W) x)) = x at hh
  refine Eq.trans ?_ hh
  apply Finset.sum_congr rfl
  intro i _
  have hs := ((SheafOfModules.ιFree i :
      SheafOfModules.unit (X.ringCatSheaf.over U) ⟶ SheafOfModules.free I).val.app (op W)).hom.map_smul
    (show Γ(X, W.left) from (freeCoordinate U I i).val.app (op W) x)
    (1 : Γ(X, W.left))
  rw [smul_eq_mul, mul_one] at hs
  exact hs.symm

/-- The canonical finite free basis on sections of the free sheaf on the
slice site of an open. -/
def freeOverSectionBasis (W : Over U) :
    Module.Basis I Γ(X, W.left)
      ((SheafOfModules.free (R := X.ringCatSheaf.over U) I).val.obj (op W)) :=
  Module.Basis.ofEquivFun
    { toFun := fun x i => (freeCoordinate U I i).val.app (op W) x
      invFun := fun c => ∑ i, c i •
        (show (SheafOfModules.free (R := X.ringCatSheaf.over U) I).val.obj (op W)
          from (SheafOfModules.freeSection i).val (op W))
      map_add' := by intros; ext i; exact map_add _ _ _
      map_smul' := by intros; ext i; exact map_smul _ _ _
      left_inv := free_expansion U I W
      right_inv := by
        intro c
        ext i
        simp only [map_sum, map_smul, freeCoordinate_freeSection]
        simp }

@[simp]
theorem freeOverSectionBasis_apply (W : Over U) (i : I) :
    freeOverSectionBasis U I W i =
      (SheafOfModules.freeSection i).val (op W) := by
  simp [freeOverSectionBasis, Module.Basis.coe_ofEquivFun]

end Free

variable {X : Scheme.{u}} {U : X.Opens}

/-- A map on the slice site is an isomorphism if it is bijective over every
affine subopen. -/
theorem isIso_of_bijective_affineOver
    {A B : SheafOfModules (X.ringCatSheaf.over U)} (φ : A ⟶ B)
    (hφ : ∀ W : Over U, IsAffineOpen W.left →
      Function.Bijective (φ.val.app (op W))) : IsIso φ := by
  let ψ := (SheafOfModules.toSheaf _).map φ
  have hsurj : Presheaf.IsLocallySurjective
      ((_root_.Opens.grothendieckTopology X).over U) ψ.hom := by
    constructor
    intro W s
    rw [GrothendieckTopology.mem_over_iff, _root_.Opens.mem_grothendieckTopology]
    intro x hx
    obtain ⟨V, hV, hxV, hVW⟩ := exists_isAffineOpen_mem_and_subset hx
    refine ⟨V, homOfLE hVW, ?_, hxV⟩
    rw [Sieve.overEquiv_iff, Presheaf.imageSieve_apply]
    let Z : Over U := Over.mk (homOfLE hVW ≫ W.hom)
    let j : Z ⟶ W := Over.homMk (homOfLE hVW)
    exact (hφ Z hV).2 (B.val.map j.op s)
  have hinj : Presheaf.IsLocallyInjective
      ((_root_.Opens.grothendieckTopology X).over U) ψ.hom := by
    constructor
    intro W a b hab
    rw [GrothendieckTopology.mem_over_iff, _root_.Opens.mem_grothendieckTopology]
    intro x hx
    obtain ⟨V, hV, hxV, hVW⟩ := exists_isAffineOpen_mem_and_subset hx
    refine ⟨V, homOfLE hVW, ?_, hxV⟩
    rw [Sieve.overEquiv_iff, Presheaf.equalizerSieve_apply]
    let Z : Over U := Over.mk (homOfLE hVW ≫ W.unop.hom)
    let j : Z ⟶ W.unop := Over.homMk (homOfLE hVW)
    apply (hφ Z hV).1
    exact (PresheafOfModules.naturality_apply φ.val j.op a).trans
      ((congrArg (B.val.map j.op) hab).trans
        (PresheafOfModules.naturality_apply φ.val j.op b).symm)
  have : IsIso ψ :=
    (Sheaf.isLocallyBijective_iff_isIso _).1
      ⟨inferInstanceAs (Presheaf.IsLocallyInjective _ ψ.hom),
        inferInstanceAs (Presheaf.IsLocallySurjective _ ψ.hom)⟩
  exact isIso_of_reflects_iso φ (SheafOfModules.toSheaf _)

section Frame

variable (M : X.Modules) (U : X.Opens) (I : Type u) [Fintype I]
    (m : I → Γ(M, U))

/-- Restrict a specified actual section to all objects of the slice site. -/
def sectionOver (x : Γ(M, U)) : (M.over U).sections :=
  PresheafOfModules.sectionsMk (fun W => M.presheaf.map W.unop.hom.op x) (by
    intro W V j
    change M.presheaf.map j.unop.left.op (M.presheaf.map W.unop.hom.op x) =
      M.presheaf.map V.unop.hom.op x
    exact (ConcreteCategory.congr_hom
      (M.presheaf.map_comp W.unop.hom.op j.unop.left.op) x).symm)

/-- The free-generator map given by specified actual sections. -/
def basisSectionsHom :
    SheafOfModules.free (R := X.ringCatSheaf.over U) I ⟶ M.over U :=
  (M.over U).freeHomEquiv.symm (fun i => sectionOver M U (m i))

omit [Fintype I] in
theorem basisSectionsHom_freeSection (W : Over U) (i : I) :
    (basisSectionsHom M U I m).val.app (op W)
        ((SheafOfModules.freeSection i).val (op W)) =
      M.presheaf.map W.hom.op (m i) := by
  exact congrArg (fun s => s.val (op W))
    (SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection
      (fun i => sectionOver M U (m i)) i)

variable
    (hb : ∀ W : Over U, IsAffineOpen W.left →
      ∃ b : Module.Basis I Γ(X, W.left) Γ(M, W.left),
        ∀ i, b i = M.presheaf.map W.hom.op (m i))

include hb in
theorem isIso_basisSectionsHom : IsIso (basisSectionsHom M U I m) := by
  apply isIso_of_bijective_affineOver
  intro W hW
  obtain ⟨b, hb⟩ := hb W hW
  let e := (freeOverSectionBasis U I W).repr.trans b.repr.symm
  have he : ((basisSectionsHom M U I m).val.app (op W)).hom = e.toLinearMap := by
    apply (freeOverSectionBasis U I W).ext
    intro i
    rw [freeOverSectionBasis_apply, basisSectionsHom_freeSection, ← hb i]
    change b i = e ((SheafOfModules.freeSection i).val (op W))
    rw [← freeOverSectionBasis_apply U I W i]
    change b i = b.repr.symm
      ((freeOverSectionBasis U I W).repr (freeOverSectionBasis U I W i))
    rw [Module.Basis.repr_self, Module.Basis.repr_symm_single_one]
  change Function.Bijective ((basisSectionsHom M U I m).val.app (op W)).hom
  rw [he]
  exact e.bijective

/-- A family of sections that forms a basis on every affine subopen gives an
actual finite free frame of the sheaf on the original open. -/
def affineBasisFrame :
    SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U :=
  @asIso _ _ _ _ (basisSectionsHom M U I m) (isIso_basisSectionsHom M U I m hb)

theorem affineBasisFrame_basis (W : Over U) (i : I) :
    localSectionBasis (affineBasisFrame M U I m hb) W i =
      M.presheaf.map W.hom.op (m i) := by
  rw [localSectionBasis_apply]
  exact basisSectionsHom_freeSection M U I m W i

end Frame

end Langlands.Scheme.Modules
