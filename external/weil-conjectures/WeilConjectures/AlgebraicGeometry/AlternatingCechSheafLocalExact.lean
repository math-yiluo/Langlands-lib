/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AlternatingCechSheafConstruction
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.AlgebraicGeometry.AlternatingCechPresheafLocalCocycles
import WeilConjectures.AlgebraicGeometry.AlternatingCechPresheafTermsSheafification
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-! # Exactness of the local alternating complex

Source: Stacks Project, Tag 02FU (cohomology-lemma-covering-resolution),
with increasing tuples as in Tag 01FM.
(blueprint: lem-pc-s3-alternating-cech-sheaf-local-exact).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem presheaf_exact_of_evaluations
    {Y : Scheme.{u}} (S : ShortComplex (PresheafOfModules.{u} Y.ringCatSheaf.obj))
    (h : ∀ V, (S.map (PresheafOfModules.evaluation _ V)).Exact) : S.Exact := by
  rw [S.leftHomologyData.exact_iff, Limits.IsZero.iff_id_eq_zero]
  ext V z
  have hz := (S.leftHomologyData.exact_map_iff
    (PresheafOfModules.evaluation _ V)).mp (h V)
  have he := (Limits.IsZero.iff_id_eq_zero _).mp hz
  exact ConcreteCategory.congr_hom he z

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem alternatingCech_local_exact_nat
    {X : Scheme.{u}} {r : ℕ} (U : Fin r → X.Opens) (G : X.Modules) (i : Fin r)
    (p : ℕ) :
    let F := Scheme.Modules.restrictFunctor (U i).ι
    let C := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (alternatingCechSheafComplex U G)
    (C.sc' p (p + 1) (p + 1 + 1)).Exact := by
  classical
  dsimp only
  let F := Scheme.Modules.restrictFunctor (U i).ι
  let C := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (alternatingCechSheafComplex U G)
  let S := C.sc' p (p + 1) (p + 1 + 1)
  apply (SheafOfModules.forget _).reflects_exact_of_faithful S
  apply presheaf_exact_of_evaluations
  intro V
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro z hz
  let W := (U i).ι.opensFunctor.obj V.unop
  let L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let η := (PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).unit
  have hunit (n : ℕ) : IsIso (η.app (alternatingCechSheafPresheafTerms U G n)) :=
    alternatingCechSheafPresheafTerms_unit_isIso U G n
  let e (n : ℕ) := (η.app (alternatingCechSheafPresheafTerms U G n)).app (Opposite.op W)
  have he (n : ℕ) : Function.Bijective (e n) := by
    have : IsIso (η.app (alternatingCechSheafPresheafTerms U G n)) := hunit n
    have : IsIso (e n) := inferInstanceAs
      (IsIso ((PresheafOfModules.evaluation _ (Opposite.op W)).map
        (η.app (alternatingCechSheafPresheafTerms U G n))))
    exact ConcreteCategory.bijective_of_isIso (e n)
  obtain ⟨z₀, hz₀⟩ := (he (p + 1)).surjective z
  have hn (n : ℕ) :
      (alternatingCechSheafPresheafD U G n).app (Opposite.op W) ≫ e (n + 1) =
        e n ≫ (L.map (alternatingCechSheafPresheafD U G n)).val.app (Opposite.op W) := by
    exact congrArg (fun f ↦ f.app (Opposite.op W)) (η.naturality
      (alternatingCechSheafPresheafD U G n))
  have hd : CochainComplex.of.d (alternatingCechSheafPresheafTerms U G)
      (alternatingCechSheafPresheafD U G) (p + 1) (p + 1 + 1) =
        alternatingCechSheafPresheafD U G (p + 1) := by
    exact
      CochainComplex.of_d (alternatingCechSheafPresheafTerms U G)
        (alternatingCechSheafPresheafD U G)
        (p + 1)
  have hz₀' : (alternatingCechSheafPresheafD U G (p + 1)).app (Opposite.op W) z₀ = 0 := by
    apply (he (p + 1 + 1)).injective
    have h := ConcreteCategory.congr_hom (hn (p + 1)) z₀
    change e (p + 1 + 1) ((alternatingCechSheafPresheafD U G (p + 1)).app
      (Opposite.op W) z₀) =
        (L.map (alternatingCechSheafPresheafD U G (p + 1))).val.app (Opposite.op W)
          (e (p + 1) z₀) at h
    rw [hz₀] at h
    have hz' : (L.map (alternatingCechSheafPresheafD U G (p + 1))).val.app
        (Opposite.op W) z = 0 := by
      change (F.map (L.map (CochainComplex.of.d
        (alternatingCechSheafPresheafTerms U G)
        (alternatingCechSheafPresheafD U G) (p + 1) (p + 1 + 1)))).val.app V z = 0 at hz
      rw [hd] at hz
      exact hz
    change _ = (e (p + 1 + 1)).hom 0
    rw [map_zero]
    exact h.trans hz'
  obtain ⟨y₀, hy₀⟩ := alternatingCechSheafPresheaf_local_cocycles U G i p W
    (by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact y.property) z₀ hz₀'
  refine ⟨e p y₀, ?_⟩
  have h := ConcreteCategory.congr_hom (hn p) y₀
  change e (p + 1) ((alternatingCechSheafPresheafD U G p).app (Opposite.op W) y₀) =
    (L.map (alternatingCechSheafPresheafD U G p)).val.app (Opposite.op W) (e p y₀) at h
  rw [hy₀, hz₀] at h
  change (F.map (L.map (CochainComplex.of.d
    (alternatingCechSheafPresheafTerms U G)
    (alternatingCechSheafPresheafD U G) p (p + 1)))).val.app V (e p y₀) = z
  rw [CochainComplex.of_d]
  exact h.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Positive-degree local exactness, without choosing any splittings.
Source: Stacks Project, Tag 02FU (cohomology-lemma-covering-resolution),
adapted to the increasing-tuple convention of Tag 01FM.
(blueprint: lem-pc-s3-alternating-cech-sheaf-local-exact).

Proof: On an open V contained in U i, let z be a positive-degree cocycle.
For an increasing tuple t omitting i, define its primitive by the coordinate
of z obtained by inserting i in position b, multiplied by (-1)^b.
For a tuple containing i, set the primitive coordinate to zero. Insertion
leaves V intersect the tuple intersection unchanged, so these are linear
maps commuting with restrictions. The cocycle equation evaluated on the
inserted tuple says that the signed face sum of this primitive is z:
the face deleting i has coefficient (-1)^b twice and all other faces give
the cocycle equation. For a tuple containing i, the only nonzero face is
its deletion of i, again with sign squared equal to one. Thus the kernel
of each positive differential is the image of the preceding differential
on every test open. The intersection presheaf V ↦ G(V intersect W) is
already a sheaf: it is the direct image of the restriction to W. Its finite
products are sheaves as well. Hence the sheafification unit on each term is
an isomorphism, natural with respect to the face differential. Restrict
these units to U i to identify the specified sheaf complex with the complex
just computed. Kernel sheaves are sectionwise kernels, and the sectionwise
boundary formula makes the map to the kernel an epimorphism. Transport along
extendXIso identifies the adjacent integer degrees with these nonnegative
degrees. This proves exactness of the indicated short complex. No degree-zero
assertion or splitting is used. If V is empty all sections vanish; if r=0
there is no i; beyond the maximum tuple length the middle term is zero. -/
theorem alternatingCechSheaf_restrict_local_exact
    {X : Scheme.{u}} {r : ℕ} (U : Fin r → X.Opens) (G : X.Modules) (i : Fin r)
    (k : ℤ) :
    let F := Scheme.Modules.restrictFunctor (U i).ι
    let C := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((alternatingCechSheafComplex U G).extend ComplexShape.embeddingUpNat)
    0 < k → (C.sc' (k - 1) k (k + 1)).Exact := by
  classical
  dsimp only
  let F := Scheme.Modules.restrictFunctor (U i).ι
  let K := alternatingCechSheafComplex U G
  let C := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (K.extend ComplexShape.embeddingUpNat)
  intro hk
  obtain ⟨p, hp⟩ : ∃ p : ℕ, (p : ℤ) + 1 = k := by
    exact ⟨(k - 1).toNat, by omega⟩
  let D := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K
  have h₀ : ComplexShape.embeddingUpNat.f p = k - 1 := by simp; omega
  have h₁ : ComplexShape.embeddingUpNat.f (p + 1) = k := by simp; omega
  have h₂ : ComplexShape.embeddingUpNat.f (p + 1 + 1) = k + 1 := by simp; omega
  let e : C.sc' (k - 1) k (k + 1) ≅ D.sc' p (p + 1) (p + 1 + 1) :=
    ShortComplex.isoMk
      (F.mapIso (K.extendXIso ComplexShape.embeddingUpNat h₀))
      (F.mapIso (K.extendXIso ComplexShape.embeddingUpNat h₁))
      (F.mapIso (K.extendXIso ComplexShape.embeddingUpNat h₂))
      (by
        change F.map _ ≫ F.map _ = F.map _ ≫ F.map _
        rw [← F.map_comp, ← F.map_comp]
        congr 1
        rw [K.extend_d_eq ComplexShape.embeddingUpNat h₀ h₁]
        simp)
      (by
        change F.map _ ≫ F.map _ = F.map _ ≫ F.map _
        rw [← F.map_comp, ← F.map_comp]
        congr 1
        rw [K.extend_d_eq ComplexShape.embeddingUpNat h₁ h₂]
        simp)
  exact ShortComplex.exact_of_iso e.symm (alternatingCech_local_exact_nat U G i p)

end AlgebraicGeometry
