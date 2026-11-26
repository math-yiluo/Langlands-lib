import Langlands.AlgebraicGeometry.AffineChartPoints
import Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof
import Langlands.AlgebraicGeometry.SquareZeroAffinePairs
import Langlands.GroupScheme.AffinePoints
import Mathlib.LinearAlgebra.TensorProduct.Lift
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.TensorProduct.Finite

/-! # Coordinates of split infinitesimal points at a rational section -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.AlgebraicGeometry.SplitInfinitesimalCoordinates

open SquareZeroAffinePairs
open scoped SquareZeroAffinePairs
open SmoothProperConnectedGlobalFunctionsProof (secHom)

variable {k : Type u} [Field k]

/-- An affine test over the spectrum of the field. -/
abbrev test (D : Type u) [CommRing D] [Algebra k D] : Over (Spec (CommRingCat.of k)) :=
  (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of (CommRingCat.of k) D))

/-- Restriction of such tests along an algebra map. -/
abbrev affineTestMap {D E : Type u} [CommRing D] [CommRing E] [Algebra k D] [Algebra k E]
    (f : D →ₐ[k] E) : test (k := k) E ⟶ test (k := k) D :=
  (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom (R := CommRingCat.of k) f).op

lemma affineTestMap_comp {D E F : Type u} [CommRing D] [CommRing E] [CommRing F]
    [Algebra k D] [Algebra k E] [Algebra k F] (f : D →ₐ[k] E) (g : E →ₐ[k] F) :
    affineTestMap (g.comp f) = affineTestMap g ≫ affineTestMap f := by
  exact (algSpec (CommRingCat.of k)).map_comp (CommAlgCat.ofHom g).op (CommAlgCat.ofHom f).op

/-- An affine neighbourhood of a rational point with its augmentation. -/
structure PointChart (Y : Over (Spec (CommRingCat.of k))) (e : test (k := k) k ⟶ Y) where
  A : Type u
  [ring : CommRing A]
  [algebra : Algebra k A]
  [finiteType : Algebra.FiniteType k A]
  j : test A ⟶ Y
  [openImmersion : IsOpenImmersion j.left]
  ε : A →ₐ[k] k
  point : affineTestMap ε ≫ j = e

attribute [instance] PointChart.ring PointChart.algebra PointChart.finiteType PointChart.openImmersion

/-- Choose an affine neighbourhood of the image of a rational point. -/
theorem PointChart.nonempty (Y : Over (Spec (CommRingCat.of k))) [Smooth Y.hom]
    (e : test (k := k) k ⟶ Y) : Nonempty (PointChart Y e) := by
  let z := IsLocalRing.closedPoint k
  obtain ⟨U, hU, hz, -⟩ := exists_isAffineOpen_mem_and_subset
    (x := e.left z) (U := (⊤ : Y.left.Opens)) trivial
  let A := Γ(Y.left, U)
  let : Algebra k A := (secHom Y.hom U).hom.toAlgebra
  have hsm : Algebra.Smooth k A := RingHom.smooth_algebraMap.mp
    (SmoothProperConnectedGlobalFunctionsProof.smooth_secHom Y.hom hU)
  have hw : hU.fromSpec ≫ Y.hom = (test (k := k) A).hom := by
    change hU.fromSpec ≫ Y.hom = specMap (secHom Y.hom U).hom
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec Y.hom (isAffineOpen_top _) hU
      (le_top.trans_eq Y.hom.preimage_top.symm)]
    change _ = Spec.map (secHom Y.hom U)
    rw [secHom, Spec.map_comp, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
  have hUe : Set.range e.left ⊆ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    rintro _ ⟨x, rfl⟩
    have : x = z := Subsingleton.elim (α := PrimeSpectrum k) _ _
    rwa [this]
  let instOpen : IsOpenImmersion hU.fromSpec := hU.isOpenImmersion_fromSpec
  let j : test (k := k) A ⟶ Y := Over.homMk hU.fromSpec hw
  let e' : test (k := k) k ⟶ test (k := k) A := Over.homMk (IsOpenImmersion.lift hU.fromSpec e.left hUe) (by
    rw [← hw, ← Category.assoc, IsOpenImmersion.lift_fac]
    exact Over.w e)
  let ε : A →ₐ[k] k := (algSpec.fullyFaithful.preimage e').unop.hom
  have he : affineTestMap ε = e' := algSpec.fullyFaithful.map_preimage e'
  refine ⟨{ A := A
            j := j
            openImmersion := by change IsOpenImmersion hU.fromSpec; infer_instance
            ε := ε
            point := ?_ }⟩
  rw [he]
  apply Over.OverMorphism.ext
  exact IsOpenImmersion.lift_fac hU.fromSpec e.left hUe

section Chart

variable {Y : Over (Spec (CommRingCat.of k))} {e : test (k := k) k ⟶ Y} (c : PointChart Y e)
  {D : Type u} [CommRing D] [Algebra k D]
  {M : Type u} [AddCommGroup M] [Module D M] [Module k M] [IsScalarTower k D M]

local notation "T" => TrivSqZeroExt D M

/-- Split infinitesimal points that reduce to the given rational section. -/
abbrev PointChart.Points (_ : PointChart Y e) := {v : test (k := k) T ⟶ Y //
  affineTestMap (TrivSqZeroExt.fstHom k D M) ≫ v = affineTestMap (Algebra.ofId k D) ≫ e}

/-- Ring representatives of the same points on the chosen affine neighbourhood. -/
abbrev PointChart.Representatives := {α : c.A →ₐ[k] T //
  (TrivSqZeroExt.fstHom k D M).comp α = (Algebra.ofId k D).comp c.ε}

private theorem projection_surjective :
    Function.Surjective (specMap (projection (C := D) (M := M))) := by
  apply specMap_surjective
  · intro a
    exact ⟨TrivSqZeroExt.inl a, rfl⟩
  · intro z hz
    refine ⟨2, ?_⟩
    have hz' : z.fst = 0 := hz
    apply TrivSqZeroExt.ext
    · simp [hz']
    · simp [hz', pow_two, TrivSqZeroExt.snd_mul]

def PointChart.ofRepresentative (α : c.Representatives (D := D) (M := M)) :
    c.Points (D := D) (M := M) := ⟨affineTestMap α.val ≫ c.j, by
  rw [← Category.assoc, ← affineTestMap_comp, α.property, affineTestMap_comp, Category.assoc, c.point]⟩

private theorem PointChart.ofRepresentative_injective :
    Function.Injective (c.ofRepresentative (D := D) (M := M)) := by
  intro x y h
  apply Subtype.ext
  apply AlgHom.toRingHom_injective
  have hl := congrArg (fun t : c.Points (D := D) (M := M) ↦ t.val.left) h
  change specMap x.val.toRingHom ≫ c.j.left = specMap y.val.toRingHom ≫ c.j.left at hl
  have : Mono c.j.left := @IsOpenImmersion.mono _ _ _ c.openImmersion
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono c.j.left).mp hl))

private theorem PointChart.ofRepresentative_surjective :
    Function.Surjective (c.ofRepresentative (D := D) (M := M)) := by
  intro v
  have hv : Set.range v.val.left ⊆ Set.range c.j.left := by
    rintro y ⟨x, rfl⟩
    obtain ⟨x₀, hx₀⟩ := projection_surjective (D := D) (M := M) x
    have h := congrArg (fun a : test (k := k) D ⟶ Y ↦ a.left x₀) v.property
    change v.val.left (specMap (projection (C := D) (M := M)) x₀) = _ at h
    rw [hx₀] at h
    have he := congrArg (fun a : test (k := k) k ⟶ Y ↦
      (affineTestMap (Algebra.ofId k D) ≫ a).left x₀) c.point
    refine ⟨(affineTestMap (Algebra.ofId k D) ≫ affineTestMap c.ε).left x₀, ?_⟩
    change (affineTestMap (Algebra.ofId k D) ≫ affineTestMap c.ε ≫ c.j).left x₀ = _
    exact he.trans h.symm
  let v' : test (k := k) T ⟶ test c.A := Over.homMk (IsOpenImmersion.lift c.j.left v.val.left hv) (by
    rw [← Over.w c.j, ← Category.assoc, IsOpenImmersion.lift_fac]
    exact Over.w v.val)
  let α : c.A →ₐ[k] T := (algSpec.fullyFaithful.preimage v').unop.hom
  have hα : affineTestMap α ≫ c.j = v.val := by
    rw [show affineTestMap α = v' from algSpec.fullyFaithful.map_preimage _]
    exact Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)
  have hα₀ : (TrivSqZeroExt.fstHom k D M).comp α = (Algebra.ofId k D).comp c.ε := by
    apply AlgHom.toRingHom_injective
    have h := (congrArg (fun a ↦ affineTestMap (TrivSqZeroExt.fstHom k D M) ≫ a) hα).trans
      (v.property.trans (congrArg (fun a ↦ affineTestMap (Algebra.ofId k D) ≫ a) c.point.symm))
    simp only [← Category.assoc, ← affineTestMap_comp] at h
    have hl := congrArg (fun a : test (k := k) D ⟶ Y ↦ a.left) h
    have : Mono c.j.left := @IsOpenImmersion.mono _ _ _ c.openImmersion
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono c.j.left).mp hl))
  exact ⟨⟨α, hα₀⟩, Subtype.ext hα⟩

/-- Restriction to an affine neighbourhood gives the unique ring representative. -/
def PointChart.representative : c.Points (D := D) (M := M) ≃
    c.Representatives (D := D) (M := M) :=
  (Equiv.ofBijective c.ofRepresentative
    ⟨c.ofRepresentative_injective, c.ofRepresentative_surjective⟩).symm

local instance (priority := 50) : Algebra c.A k := c.ε.toRingHom.toAlgebra

local instance (priority := 50) : Module c.A M := Module.compHom M c.ε.toRingHom

local instance (priority := 50) : IsScalarTower c.A k M := IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)

local instance (priority := 50) : IsScalarTower k c.A M := IsScalarTower.of_algebraMap_smul (by
  intro r x
  change c.ε (algebraMap k c.A r) • x = r • x
  rw [c.ε.commutes, Algebra.algebraMap_self, RingHom.id_apply])

/-- The cotangent space of the chosen neighbourhood at the rational point. -/
abbrev PointChart.Cotangent := k ⊗[c.A] Ω[c.A⁄k]

instance PointChart.finiteCotangent : Module.Finite k c.Cotangent := by
  change Module.Finite k (k ⊗[c.A] Ω[c.A⁄k])
  have : Algebra.FiniteType k c.A := c.finiteType
  have : Module.Finite c.A Ω[c.A⁄k] := KaehlerDifferential.finite k c.A
  exact Module.Finite.base_change c.A k Ω[c.A⁄k]

private theorem PointChart.representative_fst (α : c.Representatives (D := D) (M := M))
    (a : c.A) : (α.val a).fst = algebraMap k D (c.ε a) := AlgHom.congr_fun α.property a

private def PointChart.derivation (α : c.Representatives (D := D) (M := M)) :
    Derivation k c.A M :=
  Derivation.mk'
    { toFun := fun a ↦ (α.val a).snd
      map_add' a b := by rw [map_add, TrivSqZeroExt.snd_add]
      map_smul' r a := by
        change (α.val (r • a)).snd = r • (α.val a).snd
        rw [Algebra.smul_def, map_mul, α.val.commutes]
        change algebraMap k D r • (α.val a).snd + MulOpposite.op (α.val a).fst • (0 : M) = _
        rw [smul_zero, add_zero, algebraMap_smul D] }
    (by
      intro a b
      change (α.val (a * b)).snd = c.ε a • (α.val b).snd + c.ε b • (α.val a).snd
      rw [map_mul, TrivSqZeroExt.snd_mul, op_smul_eq_smul, c.representative_fst, c.representative_fst,
        algebraMap_smul D, algebraMap_smul D])

private def PointChart.ofDerivation (δ : Derivation k c.A M) :
    c.Representatives (D := D) (M := M) := by
  let α := (Algebra.ofId k D).comp c.ε
  refine ⟨{ toFun := fun a ↦ ⟨α a, δ a⟩
            map_zero' := TrivSqZeroExt.ext (map_zero α) (map_zero δ)
            map_one' := TrivSqZeroExt.ext (map_one α) δ.map_one_eq_zero
            map_add' a b := TrivSqZeroExt.ext (map_add α a b) (map_add δ a b)
            map_mul' a b := TrivSqZeroExt.ext (map_mul α a b) ?_
            commutes' r := TrivSqZeroExt.ext (α.commutes r) (δ.map_algebraMap r) }, ?_⟩
  · change δ (a * b) = algebraMap k D (c.ε a) • δ b +
      MulOpposite.op (algebraMap k D (c.ε b)) • δ a
    rw [op_smul_eq_smul, algebraMap_smul D, algebraMap_smul D, Derivation.leibniz]
    rfl
  · ext a
    rfl

private def PointChart.derivationEquiv :
    c.Representatives (D := D) (M := M) ≃ Derivation k c.A M where
  toFun := c.derivation
  invFun := c.ofDerivation (D := D)
  left_inv α := by
    apply Subtype.ext
    exact AlgHom.ext (fun a ↦ TrivSqZeroExt.ext (c.representative_fst α a).symm rfl)
  right_inv δ := Derivation.ext fun _ ↦ rfl

/-- Evaluation of a split infinitesimal point as a linear map out of the cotangent space. -/
def PointChart.linearCoordinates : c.Points (D := D) (M := M) ≃ (c.Cotangent →ₗ[k] M) :=
  c.representative.trans (c.derivationEquiv.trans
    ((KaehlerDifferential.linearMapEquivDerivation k c.A (M := M)).symm.toEquiv.trans
      (LinearMap.liftBaseChangeEquiv (R := c.A) (M := Ω[c.A⁄k]) (N := M) k).toEquiv))

@[simp] theorem PointChart.linearCoordinates_differential (v : c.Points (D := D) (M := M))
    (a : c.A) :
    c.linearCoordinates v (1 ⊗ₜ[c.A] KaehlerDifferential.D k c.A a) =
      ((c.representative v).val a).snd := by
  simp [PointChart.linearCoordinates, PointChart.derivationEquiv, PointChart.derivation]

private theorem PointChart.linearMap_ext {f g : c.Cotangent →ₗ[k] M}
    (h : ∀ a, f (1 ⊗ₜ[c.A] KaehlerDifferential.D k c.A a) =
      g (1 ⊗ₜ[c.A] KaehlerDifferential.D k c.A a)) : f = g := by
  apply (LinearMap.liftBaseChangeEquiv (R := c.A) (M := Ω[c.A⁄k]) (N := M) k).symm.injective
  apply (KaehlerDifferential.linearMapEquivDerivation k c.A).injective
  exact Derivation.ext h

variable {E : Type u} [CommRing E] [Algebra k E]
  {N : Type u} [AddCommGroup N] [Module E N] [Module k N] [IsScalarTower k E N]

/-- A split map over the field from a map of base algebras and its coefficient map. -/
def splitAlgMap (f : D →ₐ[k] E) (g : M →ₛₗ[f.toRingHom] N) :
    TrivSqZeroExt D M →ₐ[k] TrivSqZeroExt E N where
  __ := splitMap f.toRingHom g
  commutes' r := TrivSqZeroExt.ext (f.commutes r) (map_zero g)

theorem splitAlgMap_comp_inl (f : D →ₐ[k] E) (g : M →ₛₗ[f.toRingHom] N) :
    (splitAlgMap f g).comp (TrivSqZeroExt.inlAlgHom k D M) =
      (TrivSqZeroExt.inlAlgHom k E N).comp f := by
  apply AlgHom.ext
  intro a
  exact TrivSqZeroExt.ext rfl (map_zero g)

theorem fstHom_comp_splitAlgMap (f : D →ₐ[k] E) (g : M →ₛₗ[f.toRingHom] N) :
    (TrivSqZeroExt.fstHom k E N).comp (splitAlgMap f g) =
      f.comp (TrivSqZeroExt.fstHom k D M) := rfl

/-- Restriction of a split point along a map of its coefficient tests. -/
def PointChart.mapPoints (f : D →ₐ[k] E) (g : M →ₛₗ[f.toRingHom] N)
    (v : c.Points (D := D) (M := M)) : c.Points (D := E) (M := N) :=
  ⟨affineTestMap (splitAlgMap f g) ≫ v.val, by
    rw [← Category.assoc, ← affineTestMap_comp, fstHom_comp_splitAlgMap,
      affineTestMap_comp, Category.assoc, v.property, ← Category.assoc, ← affineTestMap_comp,
      Algebra.comp_ofId]⟩

private theorem PointChart.representative_mapPoints (f : D →ₐ[k] E)
    (g : M →ₛₗ[f.toRingHom] N) (v : c.Points (D := D) (M := M)) :
    (c.representative (c.mapPoints f g v)).val = (splitAlgMap f g).comp (c.representative v).val := by
  let a := c.representative v
  have ha : (c.ofRepresentative a).val = v.val := congrArg Subtype.val
    (c.representative.symm_apply_apply v)
  let b : c.Representatives (D := E) (M := N) := ⟨(splitAlgMap f g).comp a.val, by
    rw [← AlgHom.comp_assoc, fstHom_comp_splitAlgMap, AlgHom.comp_assoc, a.property,
      ← AlgHom.comp_assoc, Algebra.comp_ofId]⟩
  have hb : c.ofRepresentative b = c.mapPoints f g v := by
    apply Subtype.ext
    change affineTestMap ((splitAlgMap f g).comp a.val) ≫ c.j =
      affineTestMap (splitAlgMap f g) ≫ v.val
    rw [affineTestMap_comp, Category.assoc, ← ha]
    rfl
  change (c.representative (c.mapPoints f g v)).val = b.val
  rw [← hb]
  exact congrArg Subtype.val (c.representative.apply_symm_apply b)

/-- Cotangent coordinates commute with the actual coefficient map. -/
theorem PointChart.linearCoordinates_mapPoints (f : D →ₐ[k] E)
    (g : M →ₛₗ[f.toRingHom] N) (v : c.Points (D := D) (M := M)) (t : c.Cotangent) :
    c.linearCoordinates (c.mapPoints f g v) t = g (c.linearCoordinates v t) := by
  let g₀ : M →ₗ[k] N :=
    { toFun := g
      map_add' := map_add g
      map_smul' r x := by
        change g (r • x) = r • g x
        rw [← algebraMap_smul D r x, map_smulₛₗ]
        change f (algebraMap k D r) • g x = r • g x
        rw [f.commutes, algebraMap_smul E] }
  suffices c.linearCoordinates (c.mapPoints f g v) = g₀.comp (c.linearCoordinates v) by
    exact congrArg (fun l : c.Cotangent →ₗ[k] N ↦ l t) this
  apply c.linearMap_ext
  intro a
  rw [LinearMap.comp_apply, c.linearCoordinates_differential, c.linearCoordinates_differential,
    c.representative_mapPoints]
  rfl

/-- The constant point over the split test. -/
def PointChart.constant : c.Points (D := D) (M := M) :=
  c.ofRepresentative ⟨(TrivSqZeroExt.inlAlgHom k D M).comp ((Algebra.ofId k D).comp c.ε), rfl⟩

@[simp] theorem PointChart.constant_val : (c.constant (D := D) (M := M)).val =
    affineTestMap (TrivSqZeroExt.inlAlgHom k D M) ≫ affineTestMap (Algebra.ofId k D) ≫ e := by
  change affineTestMap ((TrivSqZeroExt.inlAlgHom k D M).comp ((Algebra.ofId k D).comp c.ε)) ≫ c.j = _
  rw [affineTestMap_comp, affineTestMap_comp, Category.assoc, Category.assoc, c.point]

@[simp] theorem PointChart.linearCoordinates_constant :
    c.linearCoordinates (c.constant (D := D) (M := M)) = 0 := by
  apply c.linearMap_ext
  intro a
  rw [LinearMap.zero_apply, c.linearCoordinates_differential]
  change ((c.representative (c.representative.symm _)).val a).snd = 0
  rw [c.representative.apply_symm_apply]
  rfl

end Chart

end Langlands.AlgebraicGeometry.SplitInfinitesimalCoordinates
