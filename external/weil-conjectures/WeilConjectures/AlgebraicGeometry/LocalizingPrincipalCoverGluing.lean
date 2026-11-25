/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Presheaf
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.CategoryTheory.Sites.IsSheafFor
import Mathlib.AlgebraicGeometry.StructureSheaf

/-! # Unique gluing on principal affine covers

Source: Stacks Project, Tag 01HV (associated module sheaves).
(blueprint: lem-pc-localizing-principal-cover-gluing).
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- Scalar restriction and localization equivalences require additional elaboration work.
/-- A localizing module presheaf has unique gluing on every cover of one affine
open by its principal opens.
Source: Stacks Project, Tag 01HV, Lemma `lemma-spec-sheaves` (4),(5).
(blueprint: lem-pc-localizing-principal-cover-gluing).

Proof: Put A = Gamma(T,W) and N = P(W). Restrict scalars on P(D(a)) to A.
Localization uniqueness gives an A-linear equivalence e(a) from P(D(a)) to
sections of the associated module sheaf of N on Spec A over D(a), carrying the
restriction of n to the constant section n. For the maps D(ab) to D(a) and
D(b), bundle P's restrictions as A-linear maps using map_smul and map_comp.
The two composites with e(ab) agree on N, hence agree on the localized module:
in the target multiplication by ab is a unit endomorphism, so multiplication
by either a or b is a unit, and IsLocalizedModule.ext applies. This proves
compatibility with both overlap restrictions. The affine principal-cover
criterion gives Ideal.span(s) = top, hence the same principal opens cover
Spec A. Transfer the given matching family by e(a), test compatibility on
D(ab), and glue in the associated module sheaf. Its global sections are N,
so the glued section comes from n in N. Naturality and injectivity of e(a)
give all required restrictions of n. Another amalgamation yields another
global section with the same restrictions, so uniqueness in the associated
sheaf and the bijectivity of its global constant-section map prove equality.
For the empty cover the span criterion forces the zero ring, and the sheaf's
empty-cover gluing proves the same existence and uniqueness with no exception. -/
theorem isSheafFor_principalCover_of_localizing
    (T : Scheme.{u}) (P : _root_.PresheafOfModules.{u} T.ringCatSheaf.obj)
    (W : T.affineOpens)
    (hP : ∀ a : Γ(T, W.1),
      IsLocalizedModule.Away a (P.map (homOfLE (T.basicOpen_le a)).op).hom)
    (s : Set Γ(T, W.1)) (hs : (⨆ a : s, T.basicOpen a.val) = W.val) :
    Presieve.IsSheafFor
      ((((Subtype.mono_coe T.affineOpens).functor).op ⋙ P.presheaf) ⋙
        CategoryTheory.forget AddCommGrpCat.{u})
      (Presieve.ofArrows (fun a : s ↦ T.affineBasicOpen (U := W) a.val)
        (fun a ↦ homOfLE (T.affineBasicOpen_le a.val)))  := by
  classical
  let R := Γ(T, W.1)
  let N := P.obj (op W.1)
  let L (a : R) := (ModuleCat.restrictScalars
    (T.ringCatSheaf.obj.map (homOfLE (T.basicOpen_le a)).op).hom).obj
      (P.obj (op (T.basicOpen a)))
  let f (a : R) : N →ₗ[R] L a := (P.map (homOfLE (T.basicOpen_le a)).op).hom
  let (a : R) : IsLocalizedModule.Away a (f a) := hP a
  let F := (structureSheafInType R N).obj
  let e (a : R) : L a ≃ₗ[R] F.obj (op (PrimeSpectrum.basicOpen a)) :=
    IsLocalizedModule.linearEquiv (.powers a) (f a) (StructureSheaf.toOpenₗ R N _)
  have he (a : R) (n : N) : e a (f a n) = StructureSheaf.toOpenₗ R N _ n := by
    exact IsLocalizedModule.linearEquiv_apply ..
  let incl (a b : R) : T.basicOpen (a * b) ≤ T.basicOpen a := by
    rw [T.basicOpen_mul]
    exact inf_le_left
  let g (a b : R) : L a →ₗ[R] L (a * b) := {
    toFun := (P.map (homOfLE (incl a b)).op).hom
    map_add' := fun x y ↦ map_add (P.map (homOfLE (incl a b)).op).hom x y
    map_smul' := by
      intro r x
      change P.map (homOfLE (incl a b)).op
          ((T.ringCatSheaf.obj.map (homOfLE (T.basicOpen_le a)).op).hom r • x) =
        (T.ringCatSheaf.obj.map (homOfLE (T.basicOpen_le (a * b))).op).hom r •
          P.map (homOfLE (incl a b)).op x
      rw [P.map_smul]
      congr 1
      exact (congr($(T.ringCatSheaf.obj.map_comp
        (homOfLE (T.basicOpen_le a)).op (homOfLE (incl a b)).op).hom r)).symm }
  have hg (a b : R) (n : N) : g a b (f a n) = f (a * b) n := by
    exact (P.map_comp_apply
      (homOfLE (T.basicOpen_le a)).op (homOfLE (incl a b)).op n).symm
  let gm (a b : R) := ((structurePresheafInModuleCat R N).map
    (homOfLE (PrimeSpectrum.basicOpen_mul_le_left a b)).op).hom
  have hn (a b : R) (x : L a) : e (a * b) (g a b x) = gm a b (e a x) := by
    have hu : ∀ z : Submonoid.powers a,
        IsUnit ((algebraMap R
          (Module.End R (F.obj (op (PrimeSpectrum.basicOpen (a * b)))))) z) := by
      intro z
      obtain ⟨k, hk⟩ := z.property
      have hab := IsLocalizedModule.map_units
        (StructureSheaf.toOpenₗ R N (PrimeSpectrum.basicOpen (a * b)))
        (⟨a * b, ⟨1, by simp⟩⟩ : Submonoid.powers (a * b))
      have ha : IsUnit (algebraMap R
          (Module.End R (F.obj (op (PrimeSpectrum.basicOpen (a * b))))) a) := by
        exact ((Commute.all a b).map (algebraMap R _)).isUnit_mul_iff.mp
          (by simpa only [map_mul] using hab) |>.1
      rw [← hk, map_pow]
      exact ha.pow k
    have hlin : (e (a * b)).toLinearMap.comp (g a b) =
        (gm a b).comp (e a).toLinearMap := by
      apply IsLocalizedModule.ext (.powers a) (f a) hu
      ext n
      change e (a * b) (g a b (f a n)) = gm a b (e a (f a n))
      rw [hg, he, he]
      rfl
    exact congr($(hlin) x)
  let inclRight (a b : R) : T.basicOpen (a * b) ≤ T.basicOpen b := by
    rw [T.basicOpen_mul]
    exact inf_le_right
  let gRight (a b : R) : L b →ₗ[R] L (a * b) := {
    toFun := (P.map (homOfLE (inclRight a b)).op).hom
    map_add' := fun x y ↦ map_add (P.map (homOfLE (inclRight a b)).op).hom x y
    map_smul' := by
      intro r x
      change P.map (homOfLE (inclRight a b)).op
          ((T.ringCatSheaf.obj.map (homOfLE (T.basicOpen_le b)).op).hom r • x) =
        (T.ringCatSheaf.obj.map (homOfLE (T.basicOpen_le (a * b))).op).hom r •
          P.map (homOfLE (inclRight a b)).op x
      rw [P.map_smul]
      congr 1
      exact (congr($(T.ringCatSheaf.obj.map_comp
        (homOfLE (T.basicOpen_le b)).op (homOfLE (inclRight a b)).op).hom r)).symm }
  have hgRight (a b : R) (n : N) : gRight a b (f b n) = f (a * b) n := by
    exact (P.map_comp_apply
      (homOfLE (T.basicOpen_le b)).op (homOfLE (inclRight a b)).op n).symm
  let gmRight (a b : R) := ((structurePresheafInModuleCat R N).map
    (homOfLE (PrimeSpectrum.basicOpen_mul_le_right a b)).op).hom
  have hnRight (a b : R) (x : L b) : e (a * b) (gRight a b x) = gmRight a b (e b x) := by
    have hu : ∀ z : Submonoid.powers b,
        IsUnit ((algebraMap R
          (Module.End R (F.obj (op (PrimeSpectrum.basicOpen (a * b)))))) z) := by
      intro z
      obtain ⟨k, hk⟩ := z.property
      have hab := IsLocalizedModule.map_units
        (StructureSheaf.toOpenₗ R N (PrimeSpectrum.basicOpen (a * b)))
        (⟨a * b, ⟨1, by simp⟩⟩ : Submonoid.powers (a * b))
      have ha : IsUnit (algebraMap R
          (Module.End R (F.obj (op (PrimeSpectrum.basicOpen (a * b))))) b) := by
        exact ((Commute.all a b).map (algebraMap R _)).isUnit_mul_iff.mp
          (by simpa only [map_mul] using hab) |>.2
      rw [← hk, map_pow]
      exact ha.pow k
    have hlin : (e (a * b)).toLinearMap.comp (gRight a b) =
        (gmRight a b).comp (e b).toLinearMap := by
      apply IsLocalizedModule.ext (.powers b) (f b) hu
      ext n
      change e (a * b) (gRight a b (f b n)) = gmRight a b (e b (f b n))
      rw [hgRight, he, he]
      rfl
    exact congr($(hlin) x)
  have hcover : (⨆ a : s, PrimeSpectrum.basicOpen (a.val : R)) = ⊤ := by
    apply PrimeSpectrum.iSup_basicOpen_eq_top_iff.mpr
    rw [Subtype.range_val]
    exact W.property.iSup_basicOpen_eq_self_iff.mp hs
  rw [Presieve.isSheafFor_arrows_iff]
  intro x hx
  let y (a : s) := e a.val (x a)
  have hy : TopCat.Presheaf.IsCompatible F
      (fun a : s ↦ PrimeSpectrum.basicOpen (a.val : R)) y := by
    intro a b
    apply (ConcreteCategory.bijective_of_isIso
      (F.map (eqToHom (PrimeSpectrum.basicOpen_mul a.val b.val)).op)).1
    simp only [← Functor.map_comp_apply, ← op_comp]
    have hp := hx a b (T.affineBasicOpen (U := W) (a.val * b.val))
      (homOfLE (incl a.val b.val))
      (homOfLE (by change T.basicOpen (a.val * b.val) ≤ T.basicOpen b.val
                   rw [T.basicOpen_mul]; exact inf_le_right)) (Subsingleton.elim _ _)
    have hna := hn a.val b.val (x a)
    change gm a.val b.val (e a.val (x a)) = gmRight a.val b.val (e b.val (x b))
    rw [← hna]
    have hnb' := hnRight a.val b.val (x b)
    rw [← hnb']
    exact congrArg (e (a.val * b.val)) hp
  obtain ⟨t, ht, huniq⟩ := TopCat.Presheaf.IsSheaf.isSheafUniqueGluing_types
    (structureSheafInType R N).property y hy
  have ht' : ∃ n : N, StructureSheaf.toOpenₗ R N ⊤ n =
      F.map (eqToHom hcover.symm).op t := by
    exact StructureSheaf.toOpenₗ_top_bijective.2 _
  obtain ⟨n, hn'⟩ := ht'
  refine ⟨n, ?_, ?_⟩
  · intro a
    apply (e a.val).injective
    change e a.val (f a.val n) = y a
    rw [he]
    have htA := ht a
    have hconst : F.map
        (homOfLE (show PrimeSpectrum.basicOpen (a.val : R) ≤ ⊤ from le_top)).op
        (StructureSheaf.toOpenₗ R N ⊤ n) =
      StructureSheaf.toOpenₗ R N (PrimeSpectrum.basicOpen a.val) n := rfl
    rw [← hconst, hn', ← Functor.map_comp_apply]
    exact htA
  · intro n' hn''
    apply (StructureSheaf.toOpenₗ_top_bijective (R := R) (M := N)).1
    have hnt : F.map (eqToHom hcover).op (StructureSheaf.toOpenₗ R N ⊤ n') = t := by
      apply huniq
      intro a
      have hea := he a.val n'
      have hna : f a.val n' = x a := hn'' a
      rw [hna] at hea
      change F.map _ (F.map _ (StructureSheaf.toOpenₗ R N ⊤ n')) = y a
      rw [← Functor.map_comp_apply]
      exact hea.symm
    rw [hn', ← hnt, ← Functor.map_comp_apply]
    simp

end AlgebraicGeometry.Scheme.Modules
