/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.Algebra.Homology.SixFunctors.BifunctorHomHomotopyExactSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.ClosedTriangulated
import Mathlib.CategoryTheory.Triangulated.Opposite.Functor

/-! # Exactness of the native derived internal Hom in its source

Source: Stacks Project, Cohomology on Sites, Tag 08JC, and the internal-Hom
complex proof in `DerivedCategory.exists_distinguished_ihom_pre`.
-/

@[expose] public section

set_option autoImplicit false

universe c v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Functor
open CategoryTheory.Pretriangulated.Opposite

namespace DerivedCategory

section
variable (C : Type c) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [HasDerivedCategory.{v} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [BraidedCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]

private instance internalHom_additive : (MonoidalClosed.internalHom (C := C)).Additive where
  map_add := by
    intro X Y f g
    ext Z
    exact MonoidalClosed.pre_add_app f.unop g.unop Z

private instance internalHom_obj_additive (X : Cᵒᵖ) :
    (MonoidalClosed.internalHom.obj X).Additive :=
  inferInstanceAs (ihom X.unop).Additive

omit [HasDerivedCategory C] [Abelian.HasFunctorialFlatResolution C] in
private theorem model_map {P P' : CochainComplex C ℤ} (f : P ⟶ P')
    (I : CochainComplex C ℤ) :
    CochainComplex.bifunctorHomMapLeft (H := MonoidalClosed.internalHom) (Y := I) f =
      CochainComplex.internalHomPre f I := by
  apply HomologicalComplex.hom_ext
  intro n
  apply CochainComplex.internalHomObj_hom_ext
  intro p q h
  change (CochainComplex.bifunctorHomMapLeft f).f n ≫
      CochainComplex.bifunctorHomπ MonoidalClosed.internalHom P I n p q h = _
  rw [CochainComplex.bifunctorHomMapLeft_f_π]
  exact (CochainComplex.internalHomPre_f_π f I n p q h).symm

private noncomputable def modelComparison (I : CochainComplex C ℤ) [I.IsKInjective] :
    (CochainComplex.bifunctorHomHomotopyFunctor MonoidalClosed.internalHom I).leftOp ≅
      Qh.op ⋙ MonoidalClosed.internalHom.flip.obj (Q.obj I) := by
  refine NatIso.ofComponents
    (fun X ↦ asIso (qhInternalHomToIhom X.unop.as I) ≪≫
      (ihom _).mapIso ((quotientCompQhIso C).app I)) ?_
  intro X Y f
  obtain ⟨X⟩ := X
  obtain ⟨Y⟩ := Y
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  obtain ⟨P', rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
  obtain ⟨g, hg⟩ := (HomotopyCategory.quotient C (.up ℤ)).map_surjective f.unop
  have hf : f = ((HomotopyCategory.quotient C (.up ℤ)).map g).op := by
    rw [hg]
    rfl
  subst f
  change Qh.map ((HomotopyCategory.quotient C (.up ℤ)).map
      (CochainComplex.bifunctorHomMapLeft
        (H := MonoidalClosed.internalHom) (Y := I) g)) ≫ qhInternalHomToIhom P' I ≫
      (ihom _).map ((quotientCompQhIso C).hom.app I) =
    (qhInternalHomToIhom P I ≫ (ihom _).map ((quotientCompQhIso C).hom.app I)) ≫ _
  rw [model_map C, reassoc_of% qhInternalHomToIhom_naturality g I, Category.assoc]
  congr 1
  exact ((MonoidalClosed.pre _).naturality _).symm

end

/-- The native derived closed structure is exact in the contravariant variable.
Source: Stacks Project, Tag 08JC; the K-injective internal-Hom model used by
`exists_distinguished_ihom_pre`
(blueprint: lem-weil-native-internal-hom-contravariant-exact).

Proof: Choose a K-injective complex I representing W. Put F(P)=internalHomObj P I.
Its degree n is the product of [P^p,I^(p+n)], with differential
(-1)^p (d_I f_p - f_(p+1) d_P). The evaluation-adjunct comparison
qhInternalHomToIhom identifies Q F(P) naturally with native Hom(Q P,Q I).
It is an isomorphism for every P, since I is K-injective. Thus Q F sends
quasi-isomorphisms to isomorphisms and descends to the derived category.

For m in Z put q(m)=m(m-1)/2. Reindexing the factors p to p+m, with coefficient
(-1)^(m*(p+m)+q(m)), defines F(P[m]) -> F(P)[-m]. In terms of the target
factor indexed by r=p+m the coefficient is (-1)^(m*r+q(m)). Substitution
in the displayed differential proves the chain-map equation: the source term
uses d_(P[m])=(-1)^m d_P, and changing r to r+1 changes the coefficient by
(-1)^m. The inverse uses the inverse reindexing and the same unit scalars.
These maps are natural for precomposition. Two raw reindexings differ from the
sum reindexing by (-1)^(m*l). The identity q(m+l)=q(m)+q(l)+m*l cancels this
factor, including for negative integers; at zero both reindexing and sign are
identities. Applying the construction with m=-n gives the coherent CommShift
structure for the opposite-category n-shift.

Check triangles on a degreewise split sequence A -> B -> C, with retraction r
and section s in each degree. Its connecting cochain is h_p = r_(p+1) ∘ d_B ∘ s_p.
The reversed Hom sequence has retraction pre(s) and section pre(r), by
internalHomShortComplexSplitting. Its connecting cochain, tested in degree n
at the product factor C^p -> I^(p+n+1), is (-1)^(p+1) f_(p+1) h_p:
expanding section*d_F*retraction gives two terms, the first zero because
r_p ∘ s_p=0, and the second this expression. On the other hand the opposite
triangle's third arrow is h[-1].op, without an extra sign, as specified by
triangleOpEquivalence. Applying F and the comparison at m=-1 gives precisely
the same expression, since q(-1)=1. Thus the image triangle is the distinguished
triangle of the reversed split sequence, including its actual connecting arrow.
Every distinguished derived triangle is isomorphic to one represented by such
a split sequence of complexes. Localize the coherent shift comparisons, then
transport through qhInternalHomToIhom and the isomorphism Q I = W. This proves
IsTriangulated with that very CommShift structure. No boundedness, symmetry
beyond braiding, or reflexivity is used; the signs also work in characteristic two. -/
theorem nativeInternalHom_contravariant_exact
    (C : Type c) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    [HasDerivedCategory.{v} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [BraidedCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    (W : DerivedCategory C) :
    ∃ s : (MonoidalClosed.internalHom.flip.obj W).CommShift ℤ,
      letI := s
      (MonoidalClosed.internalHom.flip.obj W).IsTriangulated := by
  obtain ⟨I, hI, ⟨eI⟩⟩ := exists_iso_Q_obj_of_isKInjective W
  have := hI
  let F := (CochainComplex.bifunctorHomHomotopyFunctor MonoidalClosed.internalHom I).leftOp
  let T := MonoidalClosed.internalHom.flip.obj W
  obtain ⟨sF, hF⟩ :=
    CochainComplex.bifunctorHomHomotopyFunctor_leftOp_exact MonoidalClosed.internalHom I
  let := sF
  have := hF
  let e : F ≅ Qh.op ⋙ T := modelComparison C I ≪≫
    isoWhiskerLeft Qh.op (MonoidalClosed.internalHom.flip.mapIso eI.symm)
  let V := (HomotopyCategory.quasiIso C (.up ℤ)).op
  let : Localization.Lifting Qh.op V F T := ⟨e.symm⟩
  let sT := Functor.commShiftOfLocalization Qh.op V ℤ F T
  let := sT
  have : NatTrans.CommShift e.inv ℤ :=
    inferInstanceAs (NatTrans.CommShift (Localization.Lifting.iso Qh.op V F T).hom ℤ)
  have : NatTrans.CommShift e.hom ℤ := by
    constructor
    intro n
    ext X
    dsimp
    rw [← cancel_epi (e.inv.app (X⟦n⟧)), e.inv_hom_id_app_assoc,
      ← NatTrans.shift_app_comm_assoc e.inv, ← Functor.map_comp,
      e.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.comp_id]
  have : (Qh.op ⋙ T).IsTriangulated := Functor.isTriangulated_of_iso e
  have : Qh.op.mapArrow.EssSurj := Localization.essSurj_mapArrow Qh.op V
  exact ⟨sT, Functor.isTriangulated_of_precomp Qh.op T⟩

end DerivedCategory
