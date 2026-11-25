/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Group.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Cartier
public import WeilConjectures.AlgebraicGeometry.Modules.AmpleReduced
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# The reduced subgroup scheme

Let `G` be a group scheme locally of finite type over a perfect field `k` (e.g. an algebraically
closed one). Products of reduced `k`-schemes are reduced, so the multiplication, unit and inverse
of `G` restricted to the reduced subscheme `G_red` factor through `G_red`: it is a closed subgroup
scheme, and, being reduced, it is smooth over `k`.

This reduces the ampleness statement of Stacks 0BF7 to smooth group schemes: in characteristic
zero `G` itself is reduced by Cartier's theorem, and in characteristic `p` an ample family on
`G_red` descends to `G` along the Frobenius (Stacks 0BD4).

## Main definitions

- `AlgebraicGeometry.GrpObj.reduced`: the reduced subscheme `G_red` of `G`, as a `k`-scheme, with
  its closed immersion `AlgebraicGeometry.GrpObj.reducedι : G_red ⟶ G`; it carries a group
  structure making `reducedι` a homomorphism.

## Main statements

- `AlgebraicGeometry.smooth_of_grpObj_of_isReduced`: a reduced group scheme locally of finite type
  over a perfect field is smooth.
- `AlgebraicGeometry.GrpObj.exists_isAffineOpen_compl_support_zeroLocus_of_smooth`: if every
  smooth group scheme of finite type over an algebraically closed field `k` carries an ample
  family, so does every group scheme of finite type over `k`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

/-- A reduced group scheme locally of finite type over a perfect field is smooth: it is
geometrically reduced (`AlgebraicGeometry.GeometricallyReduced.of_perfectField`). -/
theorem smooth_of_grpObj_of_isReduced [PerfectField k] {G : Scheme.{u}} (f : G ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [GrpObj (Over.mk f)] [IsReduced G] : Smooth f :=
  have : GeometricallyReduced f := .of_perfectField f
  smooth_of_grpObj f

/-- The product of two reduced schemes locally of finite type over a perfect field `k` is
reduced. -/
instance isReduced_tensorObj_left [PerfectField k] (X Y : Over (Spec (.of k)))
    [IsReduced X.left] [IsReduced Y.left] [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] : IsReduced (X ⊗ Y).left :=
  have : GeometricallyReduced Y.hom := .of_perfectField Y.hom
  have := LocallyOfFiniteType.isLocallyNoetherian X.hom
  inferInstanceAs (IsReduced (Limits.pullback X.hom Y.hom))

instance : IsReduced (𝟙_ (Over (Spec (.of k)))).left :=
  inferInstanceAs (IsReduced (Spec (.of k)))

section Reduced

variable (G : Over (Spec (.of k)))

/-- The reduced subscheme `G_red` of a scheme `G` over `k`, as a scheme over `k`. -/
noncomputable abbrev GrpObj.reduced : Over (Spec (.of k)) :=
  Over.mk (G.left.nilradical.subschemeι ≫ G.hom)

/-- The closed immersion `G_red ⟶ G` of the reduced subscheme, as a morphism over `k`. -/
noncomputable def GrpObj.reducedι : GrpObj.reduced G ⟶ G :=
  Over.homMk G.left.nilradical.subschemeι

instance : IsClosedImmersion (GrpObj.reducedι G).left :=
  inferInstanceAs (IsClosedImmersion G.left.nilradical.subschemeι)

instance : Mono (GrpObj.reducedι G) :=
  Over.mono_of_mono_left _

instance : IsReduced (GrpObj.reduced G).left :=
  inferInstanceAs (IsReduced G.left.nilradical.subscheme)

instance [LocallyOfFiniteType G.hom] : LocallyOfFiniteType (GrpObj.reduced G).hom :=
  inferInstanceAs (LocallyOfFiniteType (G.left.nilradical.subschemeι ≫ G.hom))

instance [QuasiCompact G.hom] : QuasiCompact (GrpObj.reduced G).hom :=
  inferInstanceAs (QuasiCompact (G.left.nilradical.subschemeι ≫ G.hom))

/-- A morphism `X ⟶ G` over `k` from a reduced scheme factors (uniquely, as `G_red ⟶ G` is a
monomorphism) through the reduced subscheme `G_red`. -/
noncomputable def GrpObj.reducedLift {X : Over (Spec (.of k))} [IsReduced X.left] (f : X ⟶ G) :
    X ⟶ GrpObj.reduced G :=
  Over.homMk (IsClosedImmersion.lift G.left.nilradical.subschemeι f.left (by
      rw [Scheme.IdealSheafData.ker_subschemeι,
        Scheme.IdealSheafData.le_ker_iff_range_subset_support]
      simp))
    ((IsClosedImmersion.lift_fac_assoc _ _ _ _).trans (Over.w f))

@[reassoc (attr := simp)]
theorem GrpObj.reducedLift_reducedι {X : Over (Spec (.of k))} [IsReduced X.left] (f : X ⟶ G) :
    GrpObj.reducedLift G f ≫ GrpObj.reducedι G = f := by
  apply Over.OverMorphism.ext
  exact IsClosedImmersion.lift_fac _ _ _

variable [PerfectField k] [LocallyOfFiniteType G.hom] [GrpObj G]

open CartesianMonoidalCategory MonObj in
/-- The reduced subscheme `G_red` of a group scheme `G` locally of finite type over a perfect
field is a closed subgroup scheme: as `G_red × G_red` is reduced, the multiplication, unit and
inverse of `G` restrict to `G_red`, and the group axioms follow from those of `G` since
`G_red ⟶ G` is a monomorphism. -/
noncomputable instance : GrpObj (GrpObj.reduced G) where
  one := GrpObj.reducedLift G η[G]
  mul := GrpObj.reducedLift G ((GrpObj.reducedι G ⊗ₘ GrpObj.reducedι G) ≫ μ[G])
  inv := GrpObj.reducedLift G (GrpObj.reducedι G ≫ ι[G])
  one_mul := by
    rw [← cancel_mono (GrpObj.reducedι G)]
    simp [← lift_fst_comp_snd_comp, ← Hom.mul_def, MonObj.comp_mul, leftUnitor_hom,
      toUnit_unique _ (toUnit _), ← Hom.one_def]
  mul_one := by
    rw [← cancel_mono (GrpObj.reducedι G)]
    simp [← lift_fst_comp_snd_comp, ← Hom.mul_def, MonObj.comp_mul, rightUnitor_hom,
      toUnit_unique _ (toUnit _), ← Hom.one_def]
  mul_assoc := by
    rw [← cancel_mono (GrpObj.reducedι G)]
    simp [← lift_fst_comp_snd_comp, ← Hom.mul_def, MonObj.comp_mul, _root_.mul_assoc]
  left_inv := by
    rw [← cancel_mono (GrpObj.reducedι G)]
    simp [← lift_fst_comp_snd_comp, ← Hom.mul_def, MonObj.comp_mul, ← Hom.inv_def,
      ← Hom.one_def]
  right_inv := by
    rw [← cancel_mono (GrpObj.reducedι G)]
    simp [← lift_fst_comp_snd_comp, ← Hom.mul_def, MonObj.comp_mul, ← Hom.inv_def,
      ← Hom.one_def]

/-- The inclusion `G_red ⟶ G` of the reduced subgroup scheme is a homomorphism. -/
instance : IsMonHom (GrpObj.reducedι G) where
  one_hom := GrpObj.reducedLift_reducedι G _
  mul_hom := GrpObj.reducedLift_reducedι G _

/-- The reduced subgroup scheme `G_red` of a group scheme locally of finite type over a perfect
field is smooth. -/
instance : Smooth (GrpObj.reduced G).hom :=
  smooth_of_grpObj_of_isReduced (G.left.nilradical.subschemeι ≫ G.hom)

end Reduced

/-- **Reduction of Stacks 0BF7 to smooth group schemes.** Let `k` be algebraically closed. If
every smooth group scheme of finite type over `k` carries an invertible module with finitely many
sections whose non-vanishing loci are affine and cover it, then so does every group scheme `G` of
finite type over `k`.

In characteristic zero, `G` is reduced by Cartier's theorem
(`AlgebraicGeometry.isReduced_of_grpObj`), hence smooth. In characteristic `p`, the reduced
subgroup scheme `G_red` is smooth and carries such a family, which descends to `G` along the
Frobenius (`AlgebraicGeometry.exists_isAffineOpen_compl_support_zeroLocus_of_nilradical`,
Stacks 0BD4). -/
theorem GrpObj.exists_isAffineOpen_compl_support_zeroLocus_of_smooth [IsAlgClosed k]
    (h : ∀ (H : Over (Spec (.of k))) [GrpObj H] [LocallyOfFiniteType H.hom]
      [QuasiCompact H.hom] [Smooth H.hom],
      ∃ (L : H.left.Modules) (_ : SheafOfModules.IsInvertible.{u, u, u} L) (ι : Type u)
        (_ : Finite ι) (s : ι → (𝟙_ H.left.Modules ⟶ L)),
        (∀ i, IsAffineOpen (Scheme.Modules.Hom.zeroLocus (s i)).support.compl) ∧
          ⨆ i, (Scheme.Modules.Hom.zeroLocus (s i)).support.compl = ⊤)
    (G : Over (Spec (.of k))) [GrpObj G] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] :
    ∃ (L : G.left.Modules) (_ : SheafOfModules.IsInvertible.{u, u, u} L) (ι : Type u)
      (_ : Finite ι) (s : ι → (𝟙_ G.left.Modules ⟶ L)),
      (∀ i, IsAffineOpen (Scheme.Modules.Hom.zeroLocus (s i)).support.compl) ∧
        ⨆ i, (Scheme.Modules.Hom.zeroLocus (s i)).support.compl = ⊤ := by
  rcases CharP.char_is_prime_or_zero k (ringChar k) with hp | hp
  · have hG : (ringChar k : Γ(G.left, ⊤)) = 0 := by
      rw [← map_natCast (G.hom.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom),
        CharP.cast_eq_zero, map_zero]
    have := LocallyOfFiniteType.isLocallyNoetherian G.hom
    have := QuasiCompact.compactSpace_of_compactSpace G.hom
    exact exists_isAffineOpen_compl_support_zeroLocus_of_nilradical hp hG
      (h (GrpObj.reduced G))
  · have := ringChar.charP k
    rw [hp] at this
    have := CharP.charP_to_charZero k
    let : GrpObj (Over.mk G.hom) := inferInstanceAs (GrpObj G)
    have : IsReduced G.left := isReduced_of_grpObj G.hom
    have : Smooth G.hom := smooth_of_grpObj_of_isReduced G.hom
    exact h G

end AlgebraicGeometry
