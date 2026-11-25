/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.NativeRingedRestrictionHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.CategoryTheory.NativeRingedRestrictionHom
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.Algebra.Homology.HomComplex
import all WeilConjectures.Algebra.Homology.HomComplexProjections
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Natural transport of sheaf Hom complexes

Source: Stacks Project, Tags 08J7 and 0A95
(blueprint: lem-weil-pbc-ringed-hom-complex-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe c d vc vd r
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.NativeRestriction

attribute [local irreducible] homComplexFunctor

-- The unbounded derived comparisons require elaborating several functor structures.
/-- An additive functor preserving countable products transports Hom complexes
naturally whenever it transports ordinary sheaf Hom naturally.
Source: Stacks Project, Tags 08J7 and 0A95
(blueprint: lem-weil-pbc-ringed-hom-complex-transport).

Proof: form the product comparison in every degree, using the ordinary Hom
comparisons on its factors. The defining projection equations make this comparison
invertible. Projecting the differential square gives the two signed terms of the
Hom differential, and naturality of the ordinary comparison identifies them.
Projecting the naturality square for arbitrary cochain maps gives precomposition
and postcomposition by their degree maps; ordinary naturality identifies these too.
Thus the comparisons assemble into a natural cochain isomorphism. -/
theorem homComplex_transport
    {C : Type c} {D : Type d} [Category.{vc} C] [Category.{vd} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (R : Sheaf J CommRingCat.{max c d vc vd r}) (S : Sheaf K CommRingCat.{max c d vc vd r})
    (T : NativeModules.{max c d vc vd r, c, vc} R ⥤ NativeModules.{max c d vc vd r, d, vd} S)
      [T.Additive]
    [PreservesLimitsOfShape (Discrete ℤ) T]
    (γ : ∀ M N : NativeModules.{max c d vc vd r, c, vc} R,
      T.obj (SheafOfModules.homObj (R := R) M N) ≅
        SheafOfModules.homObj (R := S) (T.obj M) (T.obj N))
    (hγ : ∀ {M M' N N' : NativeModules.{max c d vc vd r, c, vc} R} (f : M' ⟶ M) (g : N ⟶ N'),
      T.map (SheafOfModules.homObjMap (R := R) f g) ≫ (γ M' N').hom =
        (γ M N).hom ≫ SheafOfModules.homObjMap (R := S) (T.map f) (T.map g)) :
    Nonempty (Functor.uncurry.obj (homComplexFunctor (R := R)) ⋙ complexMap T ≅
      ((complexMap T).op.prod (complexMap T)) ⋙
        Functor.uncurry.obj (homComplexFunctor (R := S))) := by
  classical
  obtain ⟨π, hπ, dπ, nπ⟩ := homComplex_projections_exists (R := R)
  obtain ⟨τ, hτ, dτ, nτ⟩ := homComplex_projections_exists (R := S)
  have hi (L M : CochainComplex (NativeModules.{max c d vc vd r, c, vc} R) ℤ) (n : ℤ) :
      ∃ a : T.obj ((homComplex (R := R) L M).X n) ≅
          (homComplex (R := S) ((complexMap T).obj L) ((complexMap T).obj M)).X n,
        ∀ p : ℤ, a.hom ≫ τ ((complexMap T).obj L) ((complexMap T).obj M) n p (p + n) rfl =
          T.map (π L M n p (p + n) rfl) ≫
            (γ (L.X p) (M.X (p + n))).hom :=
    fanIso _ _
      (isLimitFanMkObjOfIsLimit T _ _ (hπ L M n).some)
      (hτ ((complexMap T).obj L) ((complexMap T).obj M) n).some
      (fun p ↦ γ (L.X p) (M.X (p + n)))
  dsimp only [homComplex] at hi
  obtain ⟨a, ha⟩ : ∃ a : ∀ (L M : CochainComplex (NativeModules.{max c d vc vd r, c, vc} R) ℤ) (n
    : ℤ),
      T.obj ((((homComplexFunctor (R := R)).obj (op L)).obj M).X n) ≅
        (((homComplexFunctor (R := S)).obj (op ((complexMap T).obj L))).obj ((complexMap T).obj
          M)).X n,
      ∀ L M n p, (a L M n).hom ≫ τ ((complexMap T).obj L) ((complexMap T).obj M) n p (p + n) rfl =
        T.map (π L M n p (p + n) rfl) ≫
          (γ (L.X p) (M.X (p + n))).hom := by
    choose a ha using hi
    exact ⟨a, ha⟩
  have ha' (L M : CochainComplex (NativeModules.{max c d vc vd r, c, vc} R) ℤ)
      (n p q : ℤ) (hpq : p + n = q) :
      (a L M n).hom ≫ τ ((complexMap T).obj L) ((complexMap T).obj M) n p q hpq =
        T.map (π L M n p q hpq) ≫ (γ (L.X p) (M.X q)).hom := by
    subst q
    exact ha L M n p
  have comm (L M : CochainComplex (NativeModules.{max c d vc vd r, c, vc} R) ℤ)
      (n m : ℤ) (hnm : n + 1 = m) :
      (a L M n).hom ≫ (homComplex (R := S) ((complexMap T).obj L) ((complexMap T).obj M)).d n m =
        T.map ((homComplex (R := R) L M).d n m) ≫ (a L M m).hom := by
    apply (hτ ((complexMap T).obj L) ((complexMap T).obj M) m).some.hom_ext
    rintro ⟨p⟩
    change ((a L M n).hom ≫ _) ≫ τ ((complexMap T).obj L) ((complexMap T).obj M) m p (p + m) rfl =
      (T.map _ ≫ (a L M m).hom) ≫ τ ((complexMap T).obj L) ((complexMap T).obj M) m p (p + m) rfl
    have hH := dπ L M n m p (p + m) (p + n) (p + 1)
      hnm rfl rfl (by omega)
    have hK := dτ ((complexMap T).obj L) ((complexMap T).obj M) n m p (p + m) (p + n) (p + 1)
      hnm rfl rfl (by omega)
    simp only [Units.smul_def] at hH hK
    dsimp only [homComplex]
    have hh := factor_differential (C := NativeModules.{max c d vc vd r, c, vc} R) (D :=
      NativeModules.{max c d vc vd r, d, vd} S) T
      ((((homComplexFunctor (R := R)).obj (op L)).obj M).d n m)
      ((((homComplexFunctor (R := S)).obj (op ((complexMap T).obj L))).obj ((complexMap T).obj
        M)).d n m)
      (π L M n p (p + n) rfl)
      (π L M n (p + 1) (p + m) (by omega))
      (π L M m p (p + m) rfl)
      (SheafOfModules.homObjMap (R := R) (𝟙 (L.X p)) (M.d (p + n) (p + m)))
      (SheafOfModules.homObjMap (R := R) (L.d p (p + 1)) (𝟙 (M.X (p + m))))
      (τ ((complexMap T).obj L) ((complexMap T).obj M) n p (p + n) rfl)
      (τ ((complexMap T).obj L) ((complexMap T).obj M) n (p + 1) (p + m) (by omega))
      (τ ((complexMap T).obj L) ((complexMap T).obj M) m p (p + m) rfl)
      (SheafOfModules.homObjMap (R := S) (𝟙 (((complexMap T).obj L).X p))
        (((complexMap T).obj M).d (p + n) (p + m)))
      (SheafOfModules.homObjMap (R := S) (((complexMap T).obj L).d p (p + 1))
        (𝟙 (((complexMap T).obj M).X (p + m))))
      (a L M n).hom (a L M m).hom
      (γ (L.X p) (M.X (p + n))).hom
      (γ (L.X (p + 1)) (M.X (p + m))).hom
      (γ (L.X p) (M.X (p + m))).hom (n.negOnePow : ℤ) hH hK
      (ha' L M n p (p + n) rfl)
      (ha' L M n (p + 1) (p + m) (by omega))
      (ha' L M m p (p + m) rfl)
    apply hh
    · dsimp only [complexMap, Functor.mapHomologicalComplex]
      simpa only [Functor.map_id] using
        hγ (𝟙 (L.X p)) (M.d (p + n) (p + m))
    · dsimp only [complexMap, Functor.mapHomologicalComplex]
      simpa only [Functor.map_id] using
        hγ (L.d p (p + 1)) (𝟙 (M.X (p + m)))
  refine ⟨NatIso.ofComponents
    (fun X ↦ HomologicalComplex.Hom.isoOfComponents
      (a X.1.unop X.2) (comm X.1.unop X.2)) ?_⟩
  intro X Y f
  apply HomologicalComplex.Hom.ext
  funext n
  apply (hτ ((complexMap T).obj Y.1.unop) ((complexMap T).obj Y.2) n).some.hom_ext
  rintro ⟨p⟩
  have hs := nπ X.1.unop Y.1.unop X.2 Y.2 f.1.unop f.2 n p (p + n) rfl
  have ht := nτ ((complexMap T).obj X.1.unop) ((complexMap T).obj Y.1.unop)
    ((complexMap T).obj X.2) ((complexMap T).obj Y.2)
    ((complexMap T).map f.1.unop) ((complexMap T).map f.2) n p (p + n) rfl
  change (T.map
      ((((homComplexFunctor (R := R)).map f.1).app X.2 ≫
        ((homComplexFunctor (R := R)).obj Y.1).map f.2).f n) ≫
      (a Y.1.unop Y.2 n).hom) ≫
        τ ((complexMap T).obj Y.1.unop) ((complexMap T).obj Y.2) n p (p + n) rfl =
    ((a X.1.unop X.2 n).hom ≫
      ((((homComplexFunctor (R := S)).map
        ((complexMap T).map f.1.unop).op).app ((complexMap T).obj X.2) ≫
        ((homComplexFunctor (R := S)).obj
          (op ((complexMap T).obj Y.1.unop))).map ((complexMap T).map f.2)).f n)) ≫
      τ ((complexMap T).obj Y.1.unop) ((complexMap T).obj Y.2) n p (p + n) rfl
  simp only [Category.assoc]
  rw [ha', ht]
  conv_rhs => rw [← Category.assoc, ha']
  rw [← T.map_comp_assoc]
  erw [hs]
  simp only [T.map_comp, Category.assoc]
  exact congrArg (fun t ↦ T.map (π X.1.unop X.2 n p (p + n) rfl) ≫ t)
    (hγ (f.1.unop.f p) (f.2.f (p + n)))

end CategoryTheory.NativeRestriction
