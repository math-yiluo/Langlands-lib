/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.DualNumber
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import WeilConjectures.Mathlib.Algebra.DualNumber
public import WeilConjectures.Mathlib.RingTheory.DualNumber

/-!
# Dual-number thickenings of schemes

For a scheme `X`, the *dual-number thickening* `X[ε]` is the scheme with the same underlying
space as `X` and structure sheaf `𝒪_X[ε] = 𝒪_X ⊕ ε𝒪_X`, `ε² = 0`: the relative spectrum of the
sheaf of algebras `𝒪_X[ε]`, equivalently the fibre product `X ×_ℤ Spec ℤ[ε]`. Its sections over an
open `U` are, by definition, the dual numbers `Γ(X, U)[ε]` over `Γ(X, U)`. It comes with the
projection `p : X[ε] ⟶ X` (inclusion of constants), the closed immersion `i : X ⟶ X[ε]` (`ε ↦ 0`)
with `i ≫ p = 𝟙`, functoriality `f[ε] : X[ε] ⟶ Y[ε]` for `f : X ⟶ Y`, and the two-parameter
thickening `X[ε][δ]` with the map `X[ε][δ] ⟶ X[η]`, `η ↦ εδ`, which records the mixed infinitesimal
term.

Points of a scheme `G` with values in `S[ε]` reducing to a given point along `i` are the tangent
vectors of `G` at that point; for a group scheme this is the Lie algebra, see
`WeilConjectures.AlgebraicGeometry.GroupScheme.Lie`. For `S = Spec k`, the canonical morphism
`(Spec k)[ε] ⟶ Spec k[ε]` is an isomorphism, identifying these points with the points of `G` with
values in the ring `k[ε]`.

## Main definitions

- `DualNumber.mapRingHom`: functoriality of dual numbers in ring homomorphisms, and the functor
  `CommRingCat.dualNumber` with the natural transformations `dualNumberInl` (constants),
  `dualNumberFst` (`ε ↦ 0`) and `dualNumberMul` (`η ↦ εδ`).
- `AlgebraicGeometry.Scheme.dualNumbers`: the thickening `X[ε]`.
- `AlgebraicGeometry.Scheme.dualNumbersProj`, `AlgebraicGeometry.Scheme.dualNumbersι`: the
  projection `X[ε] ⟶ X` and the closed immersion `X ⟶ X[ε]`.
- `AlgebraicGeometry.Scheme.Hom.dualNumbers`: the morphism `f[ε] : X[ε] ⟶ Y[ε]`.
- `AlgebraicGeometry.Scheme.dualNumbersMul`: the map `X[ε][δ] ⟶ X[η]`, `η ↦ εδ`.
- `AlgebraicGeometry.Scheme.dualNumbersScale`: scaling the infinitesimal, `ε ↦ cε`, by a global
  section `c` of `𝒪_X`.
- `AlgebraicGeometry.Scheme.dualNumbersOver`, `AlgebraicGeometry.Scheme.dualNumbers₂Over`: the
  thickenings `S[ε]` and `S[ε][δ]` as schemes over `S`, with the morphisms above as morphisms over
  `S` (`dualNumbersιOver`, `dualNumbersScaleOver`, `dualNumbersMulOver`, ...).
- `AlgebraicGeometry.Scheme.dualNumbersToSpec`: the isomorphism `(Spec R)[ε] ⟶ Spec R[ε]`.

## Implementation notes

The thickening is first built as a locally ringed space,
`AlgebraicGeometry.LocallyRingedSpace.dualNumbers`: the stalks of `𝒪_X[ε]` are the dual numbers
over the stalks of `𝒪_X` (`TopCat.Presheaf.stalkDualNumberHom`). It is a scheme since the
thickening of an affine scheme `Z` is affine (`LocallyRingedSpace.isIso_toΓSpec_dualNumbers`):
dual numbers commute with localization, so the stalks of `Z[ε]` are the localizations of
`Γ(Z)[ε]`. The morphisms between thickenings are built by hand from their action on sections;
they are local since a germ of `𝒪_X[ε]` is a unit as soon as its constant part is
(`TopCat.Presheaf.isUnit_germ_dualNumber_iff`).

## Blueprint

- `def-wf-lie-algebra-derivation`: points with values in the dual numbers as tangent vectors.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory TopologicalSpace TrivSqZeroExt Opposite

/-! ### Dual numbers as a functor on commutative rings -/

namespace DualNumber

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

/-- A ring homomorphism `f : R → S` induces `R[ε] → S[ε]`, `a + εb ↦ f(a) + εf(b)`. -/
def mapRingHom (f : R →+* S) : R[ε] →+* S[ε] where
  toFun x := inl (f x.fst) + inr (f x.snd)
  map_one' := by ext <;> simp
  map_mul' x y := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp

@[simp]
theorem fst_mapRingHom (f : R →+* S) (x : R[ε]) : (mapRingHom f x).fst = f x.fst := by
  simp [mapRingHom]

@[simp]
theorem snd_mapRingHom (f : R →+* S) (x : R[ε]) : (mapRingHom f x).snd = f x.snd := by
  simp [mapRingHom]

theorem mapRingHom_id : mapRingHom (RingHom.id R) = RingHom.id R[ε] := by
  ext x <;> simp

theorem mapRingHom_comp (f : R →+* S) (g : S →+* T) :
    mapRingHom (g.comp f) = (mapRingHom g).comp (mapRingHom f) := by
  ext x <;> simp

theorem mapRingHom_comp_inlHom (f : R →+* S) :
    (mapRingHom f).comp (inlHom R R) = (inlHom S S).comp f := by
  ext x <;> simp

theorem fstHom_comp_mapRingHom (f : R →+* S) :
    (fstHom S S S).toRingHom.comp (mapRingHom f) = f.comp (fstHom R R R).toRingHom :=
  RingHom.ext fun x ↦ by simp

/-- Dual numbers commute with localization: if `S` is the localization of `R` at `M`, then `S[ε]`
is the localization of `R[ε]` at the elements whose constant part lies in `M`. -/
theorem isLocalization_mapRingHom [Algebra R S] (M : Submonoid R) [IsLocalization M S]
    [Algebra R[ε] S[ε]]
    (hA : algebraMap R[ε] S[ε] = mapRingHom (algebraMap R S)) :
    IsLocalization (M.comap (fstHom R R R)) S[ε] := by
  refine (isLocalization_iff _ _).mpr ⟨fun ⟨m, hm⟩ ↦ ?_, fun z ↦ ?_, fun {x y} h ↦ ?_⟩
  · rw [hA, isUnit_iff_isUnit_fst, fst_mapRingHom]
    exact IsLocalization.map_units S ⟨m.fst, hm⟩
  · obtain ⟨⟨r₁, m₁⟩, h₁⟩ := IsLocalization.surj M z.fst
    obtain ⟨⟨r₂, m₂⟩, h₂⟩ := IsLocalization.surj M z.snd
    refine ⟨(inl (r₁ * m₂) + inr (r₂ * m₁),
      ⟨inl ((m₁ * m₂ : M) : R), by simpa using M.mul_mem m₁.2 m₂.2⟩), ?_⟩
    simp only [hA] at h₁ h₂ ⊢
    ext
    · simp only [fst_mul, fst_mapRingHom, fst_inl, fst_add, fst_inr, add_zero, Submonoid.coe_mul,
        map_mul] at h₁ ⊢
      linear_combination (algebraMap R S m₂) * h₁
    · simp only [snd_mul, fst_mapRingHom, snd_mapRingHom, fst_inl, snd_inl, snd_add, snd_inr,
        Submonoid.coe_mul, map_mul, map_zero, mul_zero, zero_add] at h₂ ⊢
      linear_combination (algebraMap R S m₁) * h₂
  · have h₁ := congr(fst $h)
    have h₂ := congr(snd $h)
    simp only [hA, fst_mapRingHom, snd_mapRingHom] at h₁ h₂
    obtain ⟨⟨c₁, hc₁⟩, e₁⟩ := IsLocalization.exists_of_eq (M := M) h₁
    obtain ⟨⟨c₂, hc₂⟩, e₂⟩ := IsLocalization.exists_of_eq (M := M) h₂
    refine ⟨⟨inl (c₁ * c₂), by simpa using M.mul_mem hc₁ hc₂⟩, ?_⟩
    ext
    · simp only [fst_mul, fst_inl]
      simp only at e₁
      rw [mul_right_comm, e₁, mul_right_comm]
    · simp only [snd_mul, fst_inl, snd_inl]
      simp only at e₂
      simp only [zero_mul, add_zero]
      rw [mul_assoc, e₂, ← mul_assoc]

/-- The ring homomorphism `R[η] → R[ε][δ]`, `a + ηb ↦ a + εδ b`, recording the mixed infinitesimal
term of the two-parameter dual numbers `R[ε][δ] = R[ε, δ]/(ε², δ²)`. -/
def mulRingHom : R[ε] →+* (R[ε])[ε] where
  toFun x := inl (inl x.fst) + inr (inr x.snd)
  map_one' := by ext <;> simp
  map_mul' x y := by ext <;> simp [mul_comm]
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp

@[simp]
theorem fst_mulRingHom (x : R[ε]) : (mulRingHom x).fst = inl x.fst := by
  simp [mulRingHom]

@[simp]
theorem snd_mulRingHom (x : R[ε]) : (mulRingHom x).snd = inr x.snd := by
  simp [mulRingHom]

theorem mapRingHom_mapRingHom_comp_mulRingHom (f : R →+* S) :
    (mapRingHom (mapRingHom f)).comp mulRingHom = mulRingHom.comp (mapRingHom f) := by
  ext x <;> simp

/-- Setting `δ = 0` in `a + εδ b` gives `a`. -/
theorem fstHom_comp_mulRingHom :
    (fstHom R[ε] R[ε] R[ε]).toRingHom.comp mulRingHom =
      (inlHom R R).comp (fstHom R R R).toRingHom := by
  ext x <;> simp [mulRingHom, algebraMap_eq_inl]

/-- Setting `ε = 0` in `a + εδ b` gives `a`. -/
theorem mapRingHom_fstHom_comp_mulRingHom :
    (mapRingHom (fstHom R R R).toRingHom).comp mulRingHom =
      (inlHom R R).comp (fstHom R R R).toRingHom := by
  ext x <;> simp [mulRingHom, algebraMap_eq_inl]
/-- The ring homomorphism `R[ε][δ] → R[ε]`, `ε, δ ↦ ε`: it sends `x + yδ` to `x + y₀ε`, where `y₀`
is the constant term of `y`. -/
def foldRingHom : (R[ε])[ε] →+* R[ε] where
  toFun x := x.fst + inr x.snd.fst
  map_one' := by ext <;> simp
  map_mul' x y := by ext <;> simp; ring
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp; ring

@[simp]
theorem fst_foldRingHom (x : (R[ε])[ε]) : (foldRingHom x).fst = x.fst.fst := by
  simp [foldRingHom]

@[simp]
theorem snd_foldRingHom (x : (R[ε])[ε]) : (foldRingHom x).snd = x.fst.snd + x.snd.fst := by
  simp [foldRingHom]

theorem scale_mapRingHom (f : R →+* S) (c : R) (x : R[ε]) :
    scale (f c) (mapRingHom f x) = mapRingHom f (scale c x) := by
  ext <;> simp [map_mul]

/-- Folding the constants in `δ` is the identity: `R[ε] → R[ε][δ] → R[ε]`. -/
theorem foldRingHom_comp_inlHom : foldRingHom.comp (inlHom R[ε] R[ε]) = RingHom.id R[ε] := by
  ext x <;> simp

/-- Folding the elements of `R[δ] ⊆ R[ε][δ]` sends `δ` to `ε`. -/
theorem foldRingHom_comp_mapRingHom_inlHom :
    foldRingHom.comp (mapRingHom (inlHom R R)) = RingHom.id R[ε] := by
  ext x <;> simp


theorem foldRingHom_comp_mapRingHom_mapRingHom (f : R →+* S) :
    foldRingHom.comp (mapRingHom (mapRingHom f)) = (mapRingHom f).comp foldRingHom := by
  ext x <;> simp


end DualNumber

namespace CommRingCat

/-- The dual numbers `R ↦ R[ε]` as an endofunctor of commutative rings. -/
noncomputable def dualNumber : CommRingCat.{u} ⥤ CommRingCat.{u} where
  obj R := .of (DualNumber R)
  map f := ofHom (DualNumber.mapRingHom f.hom)
  map_id _ := by
    ext1
    exact DualNumber.mapRingHom_id
  map_comp _ _ := by
    ext1
    exact DualNumber.mapRingHom_comp _ _

/-- The inclusion of constants `R → R[ε]`, naturally in `R`. -/
noncomputable def dualNumberInl : 𝟭 CommRingCat.{u} ⟶ dualNumber where
  app R := ofHom (TrivSqZeroExt.inlHom R R)
  naturality _ _ f := hom_ext (DualNumber.mapRingHom_comp_inlHom f.hom).symm

/-- The augmentation `R[ε] → R`, `ε ↦ 0`, naturally in `R`. -/
noncomputable def dualNumberFst : dualNumber ⟶ 𝟭 CommRingCat.{u} where
  app R := ofHom (TrivSqZeroExt.fstHom R R R).toRingHom
  naturality _ _ f := hom_ext (DualNumber.fstHom_comp_mapRingHom f.hom)

/-- The map `R[η] → R[ε][δ]`, `η ↦ εδ`, naturally in `R`. -/
noncomputable def dualNumberMul : dualNumber ⟶ dualNumber ⋙ dualNumber where
  app _ := ofHom DualNumber.mulRingHom
  naturality _ _ f := hom_ext (DualNumber.mapRingHom_mapRingHom_comp_mulRingHom f.hom).symm

/-- The map `R[ε][δ] → R[ε]`, `ε, δ ↦ ε`, naturally in `R`. -/
noncomputable def dualNumberFold : dualNumber ⋙ dualNumber ⟶ dualNumber where
  app _ := ofHom DualNumber.foldRingHom
  naturality _ _ f := hom_ext (DualNumber.foldRingHom_comp_mapRingHom_mapRingHom f.hom)


theorem fst_dualNumber_map {R S : CommRingCat.{u}} (f : R ⟶ S) (x : DualNumber R) :
    (dualNumber.map f x).fst = f x.fst :=
  DualNumber.fst_mapRingHom _ _

theorem snd_dualNumber_map {R S : CommRingCat.{u}} (f : R ⟶ S) (x : DualNumber R) :
    (dualNumber.map f x).snd = f x.snd :=
  DualNumber.snd_mapRingHom _ _

end CommRingCat

/-! ### Stalks of the dual-number thickening -/

namespace TopCat.Presheaf
variable {X : TopCat.{u}} (P : X.Presheaf CommRingCat.{u}) (x : X)

/-- The comparison map from the stalk of `P[ε]` to the dual numbers over the stalk of `P`. -/
noncomputable def stalkDualNumberHom :
    stalk (P ⋙ CommRingCat.dualNumber) x ⟶ CommRingCat.dualNumber.obj (P.stalk x) :=
  colimit.post ((OpenNhds.inclusion x).op ⋙ P) CommRingCat.dualNumber

@[reassoc]
theorem germ_stalkDualNumberHom (U : Opens X) (hx : x ∈ U) :
    germ (P ⋙ CommRingCat.dualNumber) U x hx ≫ P.stalkDualNumberHom x =
      CommRingCat.dualNumber.map (P.germ U x hx) :=
  colimit.ι_post ((OpenNhds.inclusion x).op ⋙ P) CommRingCat.dualNumber (op ⟨U, hx⟩)

theorem stalkDualNumberHom_germ (U : Opens X) (hx : x ∈ U) (g : DualNumber (P.obj (op U))) :
    P.stalkDualNumberHom x (germ (P ⋙ CommRingCat.dualNumber) U x hx g) =
      DualNumber.mapRingHom (P.germ U x hx).hom g :=
  congr($(P.germ_stalkDualNumberHom x U hx) g)

@[simp]
theorem fst_stalkDualNumberHom_germ (U : Opens X) (hx : x ∈ U) (g : DualNumber (P.obj (op U))) :
    (P.stalkDualNumberHom x (germ (P ⋙ CommRingCat.dualNumber) U x hx g)).fst =
      P.germ U x hx g.fst :=
  congr(TrivSqZeroExt.fst $(P.stalkDualNumberHom_germ x U hx g)).trans
    (DualNumber.fst_mapRingHom _ _)

@[simp]
theorem snd_stalkDualNumberHom_germ (U : Opens X) (hx : x ∈ U) (g : DualNumber (P.obj (op U))) :
    (P.stalkDualNumberHom x (germ (P ⋙ CommRingCat.dualNumber) U x hx g)).snd =
      P.germ U x hx g.snd :=
  congr(TrivSqZeroExt.snd $(P.stalkDualNumberHom_germ x U hx g)).trans
    (DualNumber.snd_mapRingHom _ _)

theorem bijective_stalkDualNumberHom : Function.Bijective (P.stalkDualNumberHom x) := by
  refine ⟨(injective_iff_map_eq_zero _).mpr fun s hs ↦ ?_, fun t ↦ ?_⟩
  · obtain ⟨U, hxU, g, rfl⟩ := exists_germ_eq (P ⋙ CommRingCat.dualNumber) s
    have h₁ := congr(TrivSqZeroExt.fst $hs)
    have h₂ := congr(TrivSqZeroExt.snd $hs)
    erw [fst_stalkDualNumberHom_germ, fst_zero, ← map_zero (P.germ U x hxU).hom] at h₁
    erw [snd_stalkDualNumberHom_germ, snd_zero, ← map_zero (P.germ U x hxU).hom] at h₂
    obtain ⟨V₁, hxV₁, i₁, j₁, e₁⟩ := P.germ_eq x hxU hxU _ _ h₁
    obtain ⟨V₂, hxV₂, i₂, j₂, e₂⟩ := P.germ_eq x hxU hxU _ _ h₂
    rw [← map_zero (germ (P ⋙ CommRingCat.dualNumber) U x hxU).hom]
    refine germ_ext (P ⋙ CommRingCat.dualNumber) (V₁ ⊓ V₂) (by simp [hxV₁, hxV₂])
      (homOfLE (inf_le_left.trans i₁.le)) (homOfLE (inf_le_left.trans i₁.le)) ?_
    refine TrivSqZeroExt.ext ?_ ?_
    · have := congr(P.map (homOfLE inf_le_left : V₁ ⊓ V₂ ⟶ V₁).op $e₁)
      simp only [map_zero] at this
      refine (CommRingCat.fst_dualNumber_map _ _).trans
        (Eq.trans ?_ (CommRingCat.fst_dualNumber_map _ _).symm)
      refine (Eq.trans ?_ this).trans (map_zero _).symm
      rw [← CommRingCat.comp_apply, ← P.map_comp]
      rfl
    · have := congr(P.map (homOfLE inf_le_right : V₁ ⊓ V₂ ⟶ V₂).op $e₂)
      simp only [map_zero] at this
      refine (CommRingCat.snd_dualNumber_map _ _).trans
        (Eq.trans ?_ (CommRingCat.snd_dualNumber_map _ _).symm)
      refine (Eq.trans ?_ this).trans (map_zero _).symm
      rw [← CommRingCat.comp_apply, ← P.map_comp]
      rfl
  · obtain ⟨U₁, hxU₁, a, ha⟩ := P.exists_germ_eq t.fst
    obtain ⟨U₂, hxU₂, b, hb⟩ := P.exists_germ_eq t.snd
    refine ⟨germ (P ⋙ CommRingCat.dualNumber) (U₁ ⊓ U₂) x (by simp [hxU₁, hxU₂])
      ((P.map (homOfLE inf_le_left).op a, P.map (homOfLE inf_le_right).op b) :
        DualNumber (P.obj (op (U₁ ⊓ U₂)))), ?_⟩
    refine TrivSqZeroExt.ext ?_ ?_
    · erw [fst_stalkDualNumberHom_germ]
      simpa using ha
    · erw [snd_stalkDualNumberHom_germ]
      simpa using hb

instance isIso_stalkDualNumberHom : IsIso (P.stalkDualNumberHom x) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr (P.bijective_stalkDualNumberHom x)

/-- A germ of `P[ε]` is a unit if and only if the germ of its constant part is a unit. -/
theorem isUnit_germ_dualNumber_iff (U : Opens X) (hx : x ∈ U) (g : DualNumber (P.obj (op U))) :
    IsUnit (germ (P ⋙ CommRingCat.dualNumber) U x hx g) ↔ IsUnit (P.germ U x hx g.fst) := by
  refine (isUnit_map_iff (P.stalkDualNumberHom x).hom _).symm.trans ?_
  erw [stalkDualNumberHom_germ]
  exact (isUnit_iff_isUnit_fst (x := DualNumber.mapRingHom (P.germ U x hx).hom g)).trans
    (by rw [DualNumber.fst_mapRingHom])

variable {P} in
theorem IsSheaf.comp_dualNumber (h : P.IsSheaf) : IsSheaf (P ⋙ CommRingCat.dualNumber) := by
  rw [isSheaf_iff_isSheafUniqueGluing] at h ⊢
  intro ι U sf hsf
  have h₁ : IsCompatible P U fun i ↦ (sf i : DualNumber (P.obj (op (U i)))).fst := fun i j ↦
    (CommRingCat.fst_dualNumber_map _ _).symm.trans <|
      congr(TrivSqZeroExt.fst $(hsf i j)).trans (CommRingCat.fst_dualNumber_map _ _)
  have h₂ : IsCompatible P U fun i ↦ (sf i : DualNumber (P.obj (op (U i)))).snd := fun i j ↦
    (CommRingCat.snd_dualNumber_map _ _).symm.trans <|
      congr(TrivSqZeroExt.snd $(hsf i j)).trans (CommRingCat.snd_dualNumber_map _ _)
  obtain ⟨a, ha, ha'⟩ := h U _ h₁
  obtain ⟨b, hb, hb'⟩ := h U _ h₂
  refine ⟨((a, b) : DualNumber (P.obj (op (iSup U)))), fun i ↦ TrivSqZeroExt.ext ?_ ?_,
    fun s hs ↦ TrivSqZeroExt.ext (ha' _ fun i ↦ ?_) (hb' _ fun i ↦ ?_)⟩
  · exact (CommRingCat.fst_dualNumber_map _ _).trans (ha i)
  · exact (CommRingCat.snd_dualNumber_map _ _).trans (hb i)
  · exact (CommRingCat.fst_dualNumber_map _ _).symm.trans congr(TrivSqZeroExt.fst $(hs i))
  · exact (CommRingCat.snd_dualNumber_map _ _).symm.trans congr(TrivSqZeroExt.snd $(hs i))

end TopCat.Presheaf

namespace AlgebraicGeometry.LocallyRingedSpace

/-- The dual-number thickening `X[ε]` of a locally ringed space `X`: the same underlying space,
with structure sheaf `𝒪_X[ε]`. Its stalks are the dual numbers over the stalks of `X`. -/
noncomputable def dualNumbers (X : LocallyRingedSpace.{u}) : LocallyRingedSpace.{u} where
  carrier := X.carrier
  presheaf := X.presheaf ⋙ CommRingCat.dualNumber
  IsSheaf := X.IsSheaf.comp_dualNumber
  isLocalRing x :=
    have : IsLocalRing (CommRingCat.dualNumber.obj (X.presheaf.stalk x)) :=
      inferInstanceAs (IsLocalRing (DualNumber _))
    (X.presheaf.stalkDualNumberHom x).hom.domain_isLocalRing

/-- The dual-number thickening of an affine scheme is affine: `Z[ε] ⟶ Spec Γ(Z[ε])` is an
isomorphism. -/
theorem isIso_toΓSpec_dualNumbers (Z : Scheme.{u}) [IsAffine Z] :
    IsIso Z.toLocallyRingedSpace.dualNumbers.toΓSpec := by
  set Y := Z.toLocallyRingedSpace.dualNumbers
  have hpt (y : Z) : Y.toΓSpecFun y = PrimeSpectrum.comap (fstHom Γ(Z, ⊤) Γ(Z, ⊤) Γ(Z, ⊤)).toRingHom
      (Z.toLocallyRingedSpace.toΓSpecFun y) := by
    ext (g : DualNumber Γ(Z, ⊤))
    have h₁ := Y.notMem_prime_iff_unit_in_stalk g y
    have h₂ := Z.toLocallyRingedSpace.notMem_prime_iff_unit_in_stalk g.fst y
    change g ∈ (Y.toΓSpecFun y).asIdeal ↔ g.fst ∈ (Z.toLocallyRingedSpace.toΓSpecFun y).asIdeal
    rw [← not_iff_not]
    exact h₁.trans ((Z.presheaf.isUnit_germ_dualNumber_iff y ⊤ trivial g).trans h₂.symm)
  have hZ : IsHomeomorph Z.toLocallyRingedSpace.toΓSpecFun :=
    (TopCat.isIso_iff_isHomeomorph Z.toSpecΓ.base).mp inferInstance
  have hbase : IsHomeomorph Y.toΓSpecFun := by
    have : Y.toΓSpecFun = PrimeSpectrum.comap (fstHom Γ(Z, ⊤) Γ(Z, ⊤) Γ(Z, ⊤)).toRingHom ∘
        Z.toLocallyRingedSpace.toΓSpecFun := funext hpt
    rw [this]
    refine .comp (PrimeSpectrum.isHomeomorph_comap _ (fun x ↦ ⟨1, one_pos, ?_⟩) ?_) hZ
    · simpa using ⟨inl x, fst_inl _ _⟩
    · intro g hg
      refine ⟨2, ?_⟩
      have : g.fst = 0 := hg
      ext <;> simp [pow_two, this]
  have : IsIso Y.toΓSpec.base := (TopCat.isIso_iff_isHomeomorph _).mpr hbase
  have hstalk (y : Z) : IsIso (Y.toΓSpec.stalkMap y) := by
    let q : PrimeSpectrum Γ(Z, ⊤) := Z.toLocallyRingedSpace.toΓSpecFun y
    let _ := Z.presheaf.algebra_section_stalk (⟨y, trivial⟩ : (⊤ : Z.Opens))
    have hZ : IsLocalization.AtPrime (Z.presheaf.stalk y) q.asIdeal := by
      have := (isAffineOpen_top Z).isLocalization_stalk ⟨y, trivial⟩
      convert this using 3
      exact PrimeSpectrum.ext (IsLocalization.AtPrime.under_maximalIdeal (Z.presheaf.stalk y)
        ((isAffineOpen_top Z).primeIdealOf ⟨y, trivial⟩).asIdeal)
    let _ : Algebra (DualNumber Γ(Z, ⊤)) (DualNumber (Z.presheaf.stalk y)) :=
      (DualNumber.mapRingHom (Z.presheaf.Γgerm y).hom).toAlgebra
    have h₁ :=
      DualNumber.isLocalization_mapRingHom (S := Z.presheaf.stalk y) q.asIdeal.primeCompl rfl
    let P := Y.toΓSpecFun y
    let e : Y.presheaf.stalk y ≃+* DualNumber (Z.presheaf.stalk y) :=
      RingEquiv.ofBijective (Z.presheaf.stalkDualNumberHom y).hom
        (Z.presheaf.bijective_stalkDualNumberHom y)
    let _ : Algebra (DualNumber Γ(Z, ⊤)) (Y.presheaf.stalk y) := (Y.presheaf.Γgerm y).hom.toAlgebra
    have h₂ : IsLocalization (q.asIdeal.primeCompl.comap (fstHom Γ(Z, ⊤) Γ(Z, ⊤) Γ(Z, ⊤)))
        (Y.presheaf.stalk y) :=
      IsLocalization.isLocalization_of_algEquiv _ <| AlgEquiv.ofRingEquiv (f := e.symm) fun g ↦ by
        apply e.injective
        rw [RingEquiv.apply_symm_apply]
        exact (Z.presheaf.stalkDualNumberHom_germ y ⊤ trivial g).symm
    let _ : Algebra (Γ.obj (op Y)) (Y.presheaf.stalk y) := (Y.presheaf.Γgerm y).hom.toAlgebra
    have h₂' : IsLocalization P.asIdeal.primeCompl (Y.presheaf.stalk y) := by
      have hM : P.asIdeal.primeCompl =
          q.asIdeal.primeCompl.comap (fstHom Γ(Z, ⊤) Γ(Z, ⊤) Γ(Z, ⊤)) := by
        ext g
        simp only [P, hpt]
        rfl
      rw [hM]
      exact h₂
    have h₃ : (Y.toΓSpec.stalkMap y).hom.comp (algebraMap (Γ.obj (op Y))
        ((Spec.structureSheaf (Γ.obj (op Y))).presheaf.stalk P)) =
          algebraMap (Γ.obj (op Y)) (Y.presheaf.stalk y) :=
      congrArg CommRingCat.Hom.hom (Y.toStalk_stalkMap_toΓSpec y)
    exact (ConcreteCategory.isIso_iff_bijective _).mpr
      (IsLocalization.bijective P.asIdeal.primeCompl
        (S := (Spec.structureSheaf (Γ.obj (op Y))).presheaf.stalk P) _ h₃)
  have : ∀ y : Y, IsIso (Y.toΓSpec.stalkMap y) := hstalk
  have : LocallyRingedSpace.IsOpenImmersion Y.toΓSpec :=
    LocallyRingedSpace.IsOpenImmersion.of_stalk_iso _
      (TopCat.homeoOfIso (asIso Y.toΓSpec.base)).isOpenEmbedding
  exact LocallyRingedSpace.IsOpenImmersion.to_iso _

end AlgebraicGeometry.LocallyRingedSpace

namespace AlgebraicGeometry

namespace Scheme

variable (X : Scheme.{u})

/-- The dual-number thickening `X[ε]` of a scheme `X`: the same underlying space with structure
sheaf `𝒪_X[ε] = 𝒪_X ⊕ ε𝒪_X`, the relative spectrum of the sheaf of algebras `𝒪_X[ε]`.
(blueprint: `def-wf-lie-algebra-derivation`) -/
noncomputable def dualNumbers : Scheme.{u} where
  __ := X.toLocallyRingedSpace.dualNumbers
  local_affine x := by
    obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (x := (x : X)) (U := ⊤) trivial
    have : IsAffine U := hU
    exact ⟨⟨U, hxU⟩, _, ⟨@asIso _ _ _ _ _ (LocallyRingedSpace.isIso_toΓSpec_dualNumbers U)⟩⟩

/-- The sections of `𝒪_{X[ε]}` over `U` are the dual numbers over the sections of `𝒪_X`. -/
theorem dualNumbers_obj (U : X.Opens) :
    Γ(X.dualNumbers, U) = CommRingCat.of (DualNumber Γ(X, U)) :=
  rfl


/-- The projection `p : X[ε] ⟶ X`: the identity on points and the inclusion of constants
`𝒪_X → 𝒪_X[ε]` on functions. -/
noncomputable def dualNumbersProj : X.dualNumbers ⟶ X where
  base := 𝟙 _
  c := Functor.whiskerLeft X.presheaf CommRingCat.dualNumberInl ≫
    (TopCat.Presheaf.Pushforward.id _).inv
  prop x := by
    constructor
    intro s hs
    obtain ⟨U, hxU, g, rfl⟩ := X.presheaf.exists_germ_eq s
    rw [PresheafedSpace.stalkMap_germ_apply] at hs
    obtain ⟨V, i, hxV, hV⟩ := RingedSpace.isUnit_res_of_isUnit_germ
      X.toLocallyRingedSpace.dualNumbers.toRingedSpace _ _ _ _ hs
    replace hV := isUnit_iff_isUnit_fst.mp hV
    erw [CommRingCat.fst_dualNumber_map] at hV
    have := (hV.map (X.presheaf.germ V x hxV).hom)
    erw [TopCat.Presheaf.germ_res_apply] at this
    exact this

/-- The closed immersion `i : X ⟶ X[ε]`, `ε ↦ 0`: the identity on points and the augmentation
`𝒪_X[ε] → 𝒪_X` on functions. Its ideal is the square-zero ideal `ε𝒪_X`. -/
noncomputable def dualNumbersι : X ⟶ X.dualNumbers where
  base := 𝟙 _
  c := Functor.whiskerLeft X.presheaf CommRingCat.dualNumberFst ≫
    (TopCat.Presheaf.Pushforward.id _).inv
  prop x := by
    constructor
    intro s hs
    obtain ⟨U, hxU, g, rfl⟩ := X.dualNumbers.presheaf.exists_germ_eq s
    rw [PresheafedSpace.stalkMap_germ_apply] at hs
    exact (X.presheaf.isUnit_germ_dualNumber_iff x U hxU g).mpr hs

@[reassoc (attr := simp)]
theorem dualNumbersι_comp_proj : X.dualNumbersι ≫ X.dualNumbersProj = 𝟙 X := by
  refine Scheme.Hom.ext rfl fun U ↦ ?_
  ext a : 2
  simp only [eqToHom_op, eqToHom_map, Scheme.Hom.comp_app]
  erw [eqToHom_refl, Category.comp_id]
  rfl

/-- The map `X[ε] ⟶ X[ε][δ]`, `ε, δ ↦ ε`: the identity on points, and `x + yδ ↦ x + y₀ε` on
functions, where `y₀` is the constant term of `y`. Precomposing with it multiplies a point
`S[ε] ⟶ G` depending on `ε` with one depending on `δ`. -/
noncomputable def dualNumbersFold : X.dualNumbers ⟶ X.dualNumbers.dualNumbers where
  base := 𝟙 _
  c := Functor.whiskerLeft X.presheaf CommRingCat.dualNumberFold ≫
    (TopCat.Presheaf.Pushforward.id _).inv
  prop x := by
    constructor
    intro s hs
    obtain ⟨U, hxU, g, rfl⟩ := X.dualNumbers.dualNumbers.presheaf.exists_germ_eq s
    rw [PresheafedSpace.stalkMap_germ_apply] at hs
    have h := (X.presheaf.isUnit_germ_dualNumber_iff x _ hxU _).mp hs
    erw [DualNumber.fst_foldRingHom] at h
    exact (X.dualNumbers.presheaf.isUnit_germ_dualNumber_iff x U hxU g).mpr
      ((X.presheaf.isUnit_germ_dualNumber_iff x U hxU g.fst).mpr h)

theorem dualNumbersFold_app (U : X.Opens) (a : Γ(X.dualNumbers.dualNumbers, U)) :
    X.dualNumbersFold.app U a = DualNumber.foldRingHom a :=
  rfl


@[reassoc (attr := simp)]
theorem dualNumbersFold_comp_proj : X.dualNumbersFold ≫ X.dualNumbers.dualNumbersProj = 𝟙 _ := by
  refine Scheme.Hom.ext rfl fun U ↦ ?_
  ext a : 2
  simp only [eqToHom_op, eqToHom_map, Scheme.Hom.comp_app]
  erw [eqToHom_refl, Category.comp_id]
  change DualNumber.foldRingHom (inl a) = a
  ext <;> simp


variable {X} in
/-- A morphism `X[ε] ⟶ Y` whose functions have no `ε`-part factors through the projection
`X[ε] ⟶ X`. -/
theorem eq_dualNumbersProj_comp_of_snd_eq_zero (φ : X.dualNumbers ⟶ Y)
    (h : ∀ U (a : Γ(Y, U)), (φ.app U a).snd = 0) :
    φ = X.dualNumbersProj ≫ X.dualNumbersι ≫ φ := by
  refine Scheme.Hom.ext' (LocallyRingedSpace.Hom.ext' (PresheafedSpace.ext _ _ rfl ?_))
  ext U a
  simp only [Functor.comp_obj, Functor.op_obj, eqToHom_refl, Functor.whiskerRight_id',
    TopCat.Presheaf.comp_app, TopCat.Presheaf.pushforward_obj_obj, NatTrans.id_app,
    Category.comp_id]
  change φ.app U a = inl (φ.app U a).fst
  exact TrivSqZeroExt.ext rfl (h _ a)

/-- The map `X[ε][δ] ⟶ X[η]`, `η ↦ εδ`: the identity on points, and on functions
`a + ηb ↦ a + εδb`. -/
noncomputable def dualNumbersMul : X.dualNumbers.dualNumbers ⟶ X.dualNumbers where
  base := 𝟙 _
  c := Functor.whiskerLeft X.presheaf CommRingCat.dualNumberMul ≫
    (TopCat.Presheaf.Pushforward.id _).inv
  prop x := by
    constructor
    intro s hs
    obtain ⟨U, hxU, g, rfl⟩ := X.dualNumbers.presheaf.exists_germ_eq s
    rw [PresheafedSpace.stalkMap_germ_apply] at hs
    obtain ⟨V, i, hxV, hV⟩ := RingedSpace.isUnit_res_of_isUnit_germ
      X.dualNumbers.dualNumbers.toRingedSpace _ _ _ _ hs
    replace hV := isUnit_iff_isUnit_fst.mp hV
    erw [CommRingCat.fst_dualNumber_map] at hV
    replace hV := isUnit_iff_isUnit_fst.mp hV
    erw [CommRingCat.fst_dualNumber_map] at hV
    have hV' : IsUnit (X.dualNumbers.presheaf.map i.op g) := by
      refine isUnit_iff_isUnit_fst.mpr ?_
      erw [CommRingCat.fst_dualNumber_map]
      convert hV using 2
      exact (congr(fst $(DualNumber.fst_mulRingHom g)).trans (fst_inl _ _)).symm
    have := (hV'.map (X.dualNumbers.presheaf.germ V x hxV).hom)
    erw [TopCat.Presheaf.germ_res_apply] at this
    exact this

variable {X} {Y : Scheme.{u}}

/-- Functoriality of the thickening: `f[ε] : X[ε] ⟶ Y[ε]` for `f : X ⟶ Y`, acting on functions by
`a + εb ↦ f^♯(a) + εf^♯(b)`. -/
noncomputable def Hom.dualNumbers (f : X ⟶ Y) : X.dualNumbers ⟶ Y.dualNumbers where
  base := f.base
  c := Functor.whiskerRight f.c CommRingCat.dualNumber
  prop x := by
    constructor
    intro s hs
    obtain ⟨U, hxU, g, rfl⟩ := Y.dualNumbers.presheaf.exists_germ_eq s
    rw [PresheafedSpace.stalkMap_germ_apply] at hs
    have h := (X.presheaf.isUnit_germ_dualNumber_iff x _ hxU _).mp hs
    erw [CommRingCat.fst_dualNumber_map] at h
    erw [← PresheafedSpace.stalkMap_germ_apply] at h
    exact (Y.presheaf.isUnit_germ_dualNumber_iff _ U hxU g).mpr
      ((isUnit_map_iff (f.toLRSHom.stalkMap x).hom _).mp h)

@[reassoc (attr := simp)]
theorem Hom.dualNumbers_comp_proj (f : X ⟶ Y) :
    f.dualNumbers ≫ Y.dualNumbersProj = X.dualNumbersProj ≫ f := by
  refine Scheme.Hom.ext rfl fun U ↦ ?_
  ext a : 2
  simp only [eqToHom_op, eqToHom_map, Scheme.Hom.comp_app]
  erw [eqToHom_refl, Category.comp_id]
  change DualNumber.mapRingHom (f.app U).hom (inl a) = inl (f.app U a)
  ext <;> simp

@[reassoc (attr := simp)]
theorem Hom.ι_comp_dualNumbers (f : X ⟶ Y) :
    X.dualNumbersι ≫ f.dualNumbers = f ≫ Y.dualNumbersι := by
  refine Scheme.Hom.ext rfl fun U ↦ ?_
  ext a : 2
  simp only [eqToHom_op, eqToHom_map, Scheme.Hom.comp_app]
  erw [eqToHom_refl, Category.comp_id]
  change (DualNumber.mapRingHom (f.app U).hom a).fst = f.app U a.fst
  simp

theorem Hom.dualNumbers_id : Hom.dualNumbers (𝟙 X) = 𝟙 X.dualNumbers := by
  refine Scheme.Hom.ext rfl fun U ↦ ?_
  ext a : 2
  simp only [eqToHom_op, eqToHom_map]
  erw [eqToHom_refl, Category.comp_id]
  change DualNumber.mapRingHom (𝟙 _ : Γ(X, U) ⟶ _).hom a = a
  ext <;> simp

theorem Hom.dualNumbers_comp {Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).dualNumbers = f.dualNumbers ≫ g.dualNumbers := by
  refine Scheme.Hom.ext rfl fun U ↦ ?_
  ext a : 2
  simp only [eqToHom_op, eqToHom_map, Scheme.Hom.comp_app]
  erw [eqToHom_refl, Category.comp_id]
  change DualNumber.mapRingHom (g.app U ≫ f.app _).hom a =
    DualNumber.mapRingHom (f.app _).hom (DualNumber.mapRingHom (g.app U).hom a)
  ext <;> simp

@[reassoc (attr := simp)]
theorem dualNumbersFold_comp_proj_dualNumbers (X : Scheme.{u}) :
    X.dualNumbersFold ≫ X.dualNumbersProj.dualNumbers = 𝟙 _ := by
  refine Scheme.Hom.ext rfl fun U ↦ ?_
  ext a : 2
  simp only [eqToHom_op, eqToHom_map, Scheme.Hom.comp_app]
  erw [eqToHom_refl, Category.comp_id]
  change DualNumber.foldRingHom (DualNumber.mapRingHom (TrivSqZeroExt.inlHom _ _) a) = a
  ext <;> simp

@[reassoc (attr := simp)]
theorem dualNumbersMul_comp_proj (X : Scheme.{u}) :
    X.dualNumbersMul ≫ X.dualNumbersProj = X.dualNumbers.dualNumbersProj ≫ X.dualNumbersProj := by
  refine Scheme.Hom.ext rfl fun U ↦ ?_
  ext a : 2
  simp only [eqToHom_op, eqToHom_map, Scheme.Hom.comp_app]
  erw [eqToHom_refl, Category.comp_id]
  change (DualNumber.mulRingHom (inl a) : DualNumber (DualNumber Γ(X, U))) = inl (inl a)
  ext <;> simp

/-- Setting `δ = 0` in `η ↦ εδ`: the composite `X[ε] ⟶ X[ε][δ] ⟶ X[η]` factors through `X`. -/
@[reassoc]
theorem dualNumbersι_comp_dualNumbersMul (X : Scheme.{u}) :
    X.dualNumbers.dualNumbersι ≫ X.dualNumbersMul = X.dualNumbersProj ≫ X.dualNumbersι := by
  refine Scheme.Hom.ext rfl fun U ↦ ?_
  rw [Subsingleton.elim (eqToHom _) (𝟙 _), CategoryTheory.op_id]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  simp only [dualNumbersProj, dualNumbersι, Hom.comp_base, dualNumbersMul, Opens.map_comp_obj,
    Hom.app, TopCat.Presheaf.comp_app, Functor.comp_obj, TopCat.Presheaf.pushforward_obj_obj,
    Functor.whiskerLeft_app, TopCat.Presheaf.Pushforward.id_inv_app, Category.comp_id,
    Functor.id_obj, Hom.comp_app]
  ext1
  exact DualNumber.fstHom_comp_mulRingHom

/-- Setting `ε = 0` in `η ↦ εδ`: the composite `X[δ] ⟶ X[ε][δ] ⟶ X[η]` factors through `X`. -/
@[reassoc]
theorem Hom.dualNumbers_dualNumbersι_comp_dualNumbersMul (X : Scheme.{u}) :
    X.dualNumbersι.dualNumbers ≫ X.dualNumbersMul = X.dualNumbersProj ≫ X.dualNumbersι := by
  refine Scheme.Hom.ext rfl fun U ↦ ?_
  rw [Subsingleton.elim (eqToHom _) (𝟙 _), CategoryTheory.op_id]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  simp only [dualNumbersProj, dualNumbersι, Hom.comp_base, Hom.dualNumbers, dualNumbersMul,
    Opens.map_comp_obj, Hom.app, TopCat.Presheaf.comp_app, Functor.comp_obj,
    TopCat.Presheaf.pushforward_obj_obj, Functor.whiskerLeft_app,
    TopCat.Presheaf.Pushforward.id_inv_app, Category.comp_id, Functor.whiskerRight_app,
    Functor.id_obj, Hom.comp_app]
  ext1
  exact DualNumber.mapRingHom_fstHom_comp_mulRingHom

/-- Setting `δ = 0` and then forgetting `ε`: `X[ε] ⟶ X[ε][δ] ⟶ X[δ]` factors through `X`. -/
@[reassoc]
theorem dualNumbersι_comp_proj_dualNumbers (X : Scheme.{u}) :
    X.dualNumbers.dualNumbersι ≫ X.dualNumbersProj.dualNumbers =
      X.dualNumbersProj ≫ X.dualNumbersι := by
  refine Scheme.Hom.ext rfl fun U ↦ ?_
  ext a : 2
  simp only [eqToHom_op, eqToHom_map, Scheme.Hom.comp_app]
  erw [eqToHom_refl, Category.comp_id]
  change (DualNumber.mapRingHom (TrivSqZeroExt.inlHom Γ(X, U) Γ(X, U)) a).fst = inl a.fst
  ext <;> simp

/-- Setting `ε = 0` and then forgetting `δ`: `X[δ] ⟶ X[ε][δ] ⟶ X[ε]` factors through `X`. -/
@[reassoc]
theorem Hom.dualNumbers_dualNumbersι_comp_proj (X : Scheme.{u}) :
    X.dualNumbersι.dualNumbers ≫ X.dualNumbers.dualNumbersProj =
      X.dualNumbersProj ≫ X.dualNumbersι := by
  refine Scheme.Hom.ext rfl fun U ↦ ?_
  ext a : 2
  simp only [eqToHom_op, eqToHom_map, Scheme.Hom.comp_app]
  erw [eqToHom_refl, Category.comp_id]
  change DualNumber.mapRingHom (TrivSqZeroExt.fstHom Γ(X, U) Γ(X, U) Γ(X, U)).toRingHom (inl a) =
    inl a.fst
  ext <;> simp

@[reassoc (attr := simp)]
theorem Hom.dualNumbers_dualNumbersι_comp_dualNumbers_proj (X : Scheme.{u}) :
    X.dualNumbersι.dualNumbers ≫ X.dualNumbersProj.dualNumbers = 𝟙 _ := by
  rw [← Hom.dualNumbers_comp, dualNumbersι_comp_proj, Hom.dualNumbers_id]

/-! ### Scaling the infinitesimal -/

variable (X) in
/-- Scaling the infinitesimal by a global section `c` of `𝒪_X`: the endomorphism `ε ↦ cε` of
`X[ε]`, the identity on points and `a + εb ↦ a + εcb` on functions. It is the scalar action of
`Γ(X, 𝒪_X)` on tangent vectors. -/
noncomputable def dualNumbersScale (c : Γ(X, ⊤)) : X.dualNumbers ⟶ X.dualNumbers where
  base := 𝟙 _
  c := { app := fun U ↦ CommRingCat.ofHom
            (DualNumber.scale (X.presheaf.map (homOfLE le_top : U.unop ⟶ ⊤).op c)).toRingHom
         naturality := fun U V i ↦ by
          ext g : 2
          change DualNumber.scale _ (DualNumber.mapRingHom (X.presheaf.map i).hom g) =
            DualNumber.mapRingHom (X.presheaf.map i).hom (DualNumber.scale _ g)
          ext
          · simp
          · simp only [DualNumber.snd_mapRingHom, DualNumber.snd_scale, map_mul]
            rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
            rfl } ≫ (TopCat.Presheaf.Pushforward.id _).inv
  prop x := by
    constructor
    intro s hs
    obtain ⟨U, hxU, g, rfl⟩ := X.dualNumbers.presheaf.exists_germ_eq s
    rw [PresheafedSpace.stalkMap_germ_apply] at hs
    have h := (X.presheaf.isUnit_germ_dualNumber_iff x _ hxU _).mp hs
    erw [DualNumber.fst_scale] at h
    exact (X.presheaf.isUnit_germ_dualNumber_iff x U hxU g).mpr h

@[reassoc (attr := simp)]
theorem dualNumbersScale_comp_proj (c : Γ(X, ⊤)) :
    X.dualNumbersScale c ≫ X.dualNumbersProj = X.dualNumbersProj := by
  refine Scheme.Hom.ext rfl fun U ↦ ?_
  ext a : 2
  simp only [eqToHom_op, eqToHom_map, Scheme.Hom.comp_app]
  erw [eqToHom_refl, Category.comp_id]
  change DualNumber.scale _ (inl a) = inl a
  ext <;> simp

theorem dualNumbersScale_app (c : Γ(X, ⊤)) (U : X.Opens) (a : Γ(X.dualNumbers, U)) :
    (X.dualNumbersScale c).app U a =
      DualNumber.scale (X.presheaf.map (homOfLE le_top : U ⟶ ⊤).op c) a :=
  rfl

@[reassoc (attr := simp)]
theorem dualNumbersι_comp_scale (c : Γ(X, ⊤)) :
    X.dualNumbersι ≫ X.dualNumbersScale c = X.dualNumbersι := by
  refine Scheme.Hom.ext rfl fun U ↦ ?_
  ext a : 2
  simp only [eqToHom_op, eqToHom_map, Scheme.Hom.comp_app]
  erw [eqToHom_refl, Category.comp_id]
  change (DualNumber.scale _ a).fst = a.fst
  simp

@[simp]
theorem dualNumbersScale_one : X.dualNumbersScale 1 = 𝟙 _ := by
  refine Scheme.Hom.ext rfl fun U ↦ ?_
  ext a : 2
  simp only [eqToHom_op, eqToHom_map]
  erw [eqToHom_refl, Category.comp_id]
  change DualNumber.scale _ a = a
  rw [map_one, DualNumber.scale_one]
  rfl

theorem dualNumbersScale_mul (c d : Γ(X, ⊤)) :
    X.dualNumbersScale (c * d) = X.dualNumbersScale c ≫ X.dualNumbersScale d := by
  refine Scheme.Hom.ext rfl fun U ↦ ?_
  ext a : 2
  simp only [eqToHom_op, eqToHom_map, Scheme.Hom.comp_app]
  erw [eqToHom_refl, Category.comp_id]
  change DualNumber.scale (X.presheaf.map (homOfLE le_top : U ⟶ ⊤).op (c * d)) a =
    DualNumber.scale (X.presheaf.map (homOfLE le_top : U ⟶ ⊤).op c)
      (DualNumber.scale (X.presheaf.map (homOfLE le_top : U ⟶ ⊤).op d) a)
  ext <;> simp [mul_assoc]

/-- Scaling by `0` is the composite `X[ε] ⟶ X ⟶ X[ε]`, `ε ↦ 0`. -/
theorem dualNumbersScale_zero : X.dualNumbersScale 0 = X.dualNumbersProj ≫ X.dualNumbersι := by
  refine Scheme.Hom.ext rfl fun U ↦ ?_
  ext a : 2
  simp only [eqToHom_op, eqToHom_map, Scheme.Hom.comp_app]
  erw [eqToHom_refl, Category.comp_id]
  change DualNumber.scale _ a = inl a.fst
  ext <;> simp

/-! ### The thickening as a scheme over its base -/

section Over

variable (S : Scheme.{u})

/-- The thickening `S[ε]` as a scheme over `S`, through the projection `p : S[ε] ⟶ S`. -/
noncomputable def dualNumbersOver : Over S :=
  Over.mk S.dualNumbersProj

@[simp]
theorem dualNumbersOver_left : (dualNumbersOver S).left = S.dualNumbers :=
  rfl

@[simp]
theorem dualNumbersOver_hom : (dualNumbersOver S).hom = S.dualNumbersProj :=
  rfl

/-- The two-parameter thickening `S[ε][δ]` as a scheme over `S`. -/
noncomputable def dualNumbers₂Over : Over S :=
  Over.mk (S.dualNumbers.dualNumbersProj ≫ S.dualNumbersProj)

/-- The closed immersion `i : S ⟶ S[ε]`, `ε ↦ 0`, as a morphism over `S` from the terminal
object `S` of the schemes over `S`: the `S`-point `ε ↦ 0` of `S[ε]`. -/
noncomputable def dualNumbersιOver : 𝟙_ (Over S) ⟶ dualNumbersOver S :=
  Over.homMk S.dualNumbersι S.dualNumbersι_comp_proj

@[simp]
theorem dualNumbersιOver_left : (dualNumbersιOver S).left = S.dualNumbersι :=
  rfl

/-- The projection `S[ε][δ] ⟶ S[ε]` forgetting `δ`, as a morphism over `S`. -/
noncomputable def dualNumbersProjεOver : dualNumbers₂Over S ⟶ dualNumbersOver S :=
  Over.homMk S.dualNumbers.dualNumbersProj

/-- The projection `S[ε][δ] ⟶ S[δ]` forgetting `ε`, as a morphism over `S`. -/
noncomputable def dualNumbersProjδOver : dualNumbers₂Over S ⟶ dualNumbersOver S :=
  Over.homMk S.dualNumbersProj.dualNumbers (Hom.dualNumbers_comp_proj _)

/-- The closed immersion `S[ε] ⟶ S[ε][δ]`, `δ ↦ 0`, as a morphism over `S`. -/
noncomputable def dualNumbersιεOver : dualNumbersOver S ⟶ dualNumbers₂Over S :=
  Over.homMk S.dualNumbers.dualNumbersι (by simp [dualNumbers₂Over, dualNumbersOver])

/-- The closed immersion `S[δ] ⟶ S[ε][δ]`, `ε ↦ 0`, as a morphism over `S`. -/
noncomputable def dualNumbersιδOver : dualNumbersOver S ⟶ dualNumbers₂Over S :=
  Over.homMk S.dualNumbersι.dualNumbers (by simp [dualNumbers₂Over, dualNumbersOver])

/-- The map `S[ε][δ] ⟶ S[η]`, `η ↦ εδ`, as a morphism over `S`. -/
noncomputable def dualNumbersMulOver : dualNumbers₂Over S ⟶ dualNumbersOver S :=
  Over.homMk S.dualNumbersMul S.dualNumbersMul_comp_proj

/-- Setting `δ = 0` in `η ↦ εδ` factors through the `S`-point `ε ↦ 0` of `S[η]`. -/
@[reassoc]
theorem dualNumbersιεOver_comp_dualNumbersMulOver :
    dualNumbersιεOver S ≫ dualNumbersMulOver S =
      CartesianMonoidalCategory.toUnit (dualNumbersOver S) ≫ dualNumbersιOver S := by
  ext1
  simpa [dualNumbersιεOver, dualNumbersMulOver, Over.toUnit_left] using
    S.dualNumbersι_comp_dualNumbersMul

/-- Setting `ε = 0` in `η ↦ εδ` factors through the `S`-point `ε ↦ 0` of `S[η]`. -/
@[reassoc]
theorem dualNumbersιδOver_comp_dualNumbersMulOver :
    dualNumbersιδOver S ≫ dualNumbersMulOver S =
      CartesianMonoidalCategory.toUnit (dualNumbersOver S) ≫ dualNumbersιOver S := by
  ext1
  simpa [dualNumbersιδOver, dualNumbersMulOver, Over.toUnit_left] using
    Hom.dualNumbers_dualNumbersι_comp_dualNumbersMul S

@[reassoc (attr := simp)]
theorem dualNumbersιεOver_comp_projεOver :
    dualNumbersιεOver S ≫ dualNumbersProjεOver S = 𝟙 _ := by
  ext1
  simp [dualNumbersιεOver, dualNumbersProjεOver]

@[reassoc (attr := simp)]
theorem dualNumbersιδOver_comp_projδOver :
    dualNumbersιδOver S ≫ dualNumbersProjδOver S = 𝟙 _ := by
  ext1
  simp [dualNumbersιδOver, dualNumbersProjδOver]

/-- Setting `δ = 0` and then forgetting `ε` factors through the `S`-point `ε ↦ 0` of `S[δ]`. -/
@[reassoc]
theorem dualNumbersιεOver_comp_projδOver :
    dualNumbersιεOver S ≫ dualNumbersProjδOver S =
      CartesianMonoidalCategory.toUnit (dualNumbersOver S) ≫ dualNumbersιOver S := by
  ext1
  simp [dualNumbersιεOver, dualNumbersProjδOver, Over.toUnit_left,
    S.dualNumbersι_comp_proj_dualNumbers]

/-- Setting `ε = 0` and then forgetting `δ` factors through the `S`-point `ε ↦ 0` of `S[ε]`. -/
@[reassoc]
theorem dualNumbersιδOver_comp_projεOver :
    dualNumbersιδOver S ≫ dualNumbersProjεOver S =
      CartesianMonoidalCategory.toUnit (dualNumbersOver S) ≫ dualNumbersιOver S := by
  ext1
  simp [dualNumbersιδOver, dualNumbersProjεOver, Over.toUnit_left,
    Hom.dualNumbers_dualNumbersι_comp_proj S]

/-- The map `S[ε] ⟶ S[ε][δ]`, `ε, δ ↦ ε`, as a morphism over `S`. -/
noncomputable def dualNumbersFoldOver : dualNumbersOver S ⟶ dualNumbers₂Over S :=
  Over.homMk S.dualNumbersFold (by simp [dualNumbers₂Over, dualNumbersOver])

@[reassoc (attr := simp)]
theorem dualNumbersFoldOver_comp_projεOver :
    dualNumbersFoldOver S ≫ dualNumbersProjεOver S = 𝟙 _ := by
  ext1
  simp [dualNumbersFoldOver, dualNumbersProjεOver]

@[reassoc (attr := simp)]
theorem dualNumbersFoldOver_comp_projδOver :
    dualNumbersFoldOver S ≫ dualNumbersProjδOver S = 𝟙 _ := by
  ext1
  simp [dualNumbersFoldOver, dualNumbersProjδOver]

/-- Scaling the infinitesimal by a global section `c` of `𝒪_S`, as an endomorphism of `S[ε]`
over `S`. -/
noncomputable def dualNumbersScaleOver (c : Γ(S, ⊤)) : dualNumbersOver S ⟶ dualNumbersOver S :=
  Over.homMk (S.dualNumbersScale c) (S.dualNumbersScale_comp_proj c)

@[simp]
theorem dualNumbersScaleOver_left (c : Γ(S, ⊤)) :
    (dualNumbersScaleOver S c).left = S.dualNumbersScale c :=
  rfl

@[reassoc (attr := simp)]
theorem dualNumbersιOver_comp_scaleOver (c : Γ(S, ⊤)) :
    dualNumbersιOver S ≫ dualNumbersScaleOver S c = dualNumbersιOver S := by
  ext : 1
  simp

@[simp]
theorem dualNumbersScaleOver_one : dualNumbersScaleOver S 1 = 𝟙 _ := by
  ext : 1
  simp

theorem dualNumbersScaleOver_mul (c d : Γ(S, ⊤)) :
    dualNumbersScaleOver S (c * d) = dualNumbersScaleOver S c ≫ dualNumbersScaleOver S d := by
  ext : 1
  simp [dualNumbersScale_mul]

/-- Scaling by `0` factors through the `S`-point `ε ↦ 0` of `S[ε]`. -/
theorem dualNumbersScaleOver_zero :
    dualNumbersScaleOver S 0 =
      CartesianMonoidalCategory.toUnit (dualNumbersOver S) ≫ dualNumbersιOver S := by
  ext : 1
  simp [dualNumbersScale_zero, Over.toUnit_left]

end Over

/-! ### The thickening of an affine scheme -/

variable (R : CommRingCat.{u})

/-- The canonical morphism `(Spec R)[ε] ⟶ Spec R[ε]`, corresponding to the ring isomorphism
`R[ε] ≅ Γ(Spec R, 𝒪)[ε] = Γ((Spec R)[ε], 𝒪)`. It is an isomorphism. -/
noncomputable def dualNumbersToSpec : (Spec R).dualNumbers ⟶ Spec (CommRingCat.of (DualNumber R)) :=
  (Spec R).dualNumbers.toSpecΓ ≫
    Spec.map (CommRingCat.ofHom (DualNumber.mapRingHom (Scheme.ΓSpecIso R).inv.hom))

/-- `(Spec R)[ε] ⟶ Spec R[ε]` is an isomorphism: `(Spec R)[ε]` is affine
(`LocallyRingedSpace.isIso_toΓSpec_dualNumbers`) with global sections `Γ(Spec R)[ε] ≅ R[ε]`. -/
instance isIso_dualNumbersToSpec : IsIso (dualNumbersToSpec R) := by
  have : IsIso (Spec R).dualNumbers.toSpecΓ := by
    have : IsIso (Scheme.forgetToLocallyRingedSpace.map (Spec R).dualNumbers.toSpecΓ) :=
      LocallyRingedSpace.isIso_toΓSpec_dualNumbers (Spec R)
    exact isIso_of_reflects_iso _ Scheme.forgetToLocallyRingedSpace
  have : IsIso (CommRingCat.ofHom (DualNumber.mapRingHom (Scheme.ΓSpecIso R).inv.hom)) :=
    inferInstanceAs (IsIso (CommRingCat.dualNumber.map (Scheme.ΓSpecIso R).inv))
  unfold dualNumbersToSpec
  infer_instance

/-- The isomorphism `(Spec R)[ε] ⟶ Spec R[ε]` is compatible with the projections to `Spec R`. -/
theorem dualNumbersToSpec_comp_specMap :
    dualNumbersToSpec R ≫ Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom R R)) =
      (Spec R).dualNumbersProj := by
  conv_rhs => rw [← Category.comp_id (Spec R).dualNumbersProj,
    ← toSpecΓ_SpecMap_ΓSpecIso_inv, toSpecΓ_naturality_assoc]
  rw [dualNumbersToSpec, Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 2
  ext a
  change DualNumber.mapRingHom (Scheme.ΓSpecIso R).inv.hom (inl a) =
    inl ((Scheme.ΓSpecIso R).inv a)
  ext <;> simp

/-- The isomorphism `(Spec R)[ε] ⟶ Spec R[ε]` is compatible with the closed immersions `ε ↦ 0`. -/
theorem ι_comp_dualNumbersToSpec :
    (Spec R).dualNumbersι ≫ dualNumbersToSpec R =
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) := by
  rw [dualNumbersToSpec, toSpecΓ_naturality_assoc, ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp,
    ← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun a ↦ ?_)
  change (Scheme.ΓSpecIso R).hom
    ((DualNumber.mapRingHom (Scheme.ΓSpecIso R).inv.hom a).fst) = a.fst
  simp

/-- The isomorphism `(Spec R)[ε] ⟶ Spec R[ε]` is compatible with scaling the infinitesimal. -/
theorem dualNumbersScale_comp_dualNumbersToSpec (c : R) :
    (Spec R).dualNumbersScale ((Scheme.ΓSpecIso R).inv c) ≫ dualNumbersToSpec R =
      dualNumbersToSpec R ≫ Spec.map (CommRingCat.ofHom (DualNumber.scale c).toRingHom) := by
  rw [dualNumbersToSpec, ← Category.assoc, toSpecΓ_naturality, Category.assoc, Category.assoc,
    ← Spec.map_comp, ← Spec.map_comp]
  congr 2
  refine CommRingCat.hom_ext (RingHom.ext fun a ↦ ?_)
  rw [CommRingCat.hom_comp, CommRingCat.hom_comp, RingHom.comp_apply, RingHom.comp_apply]
  change DualNumber.scale ((Spec R).presheaf.map (homOfLE le_top : (⊤ : (Spec R).Opens) ⟶ ⊤).op
    _) _ = _
  rw [show (homOfLE le_top : (⊤ : (Spec R).Opens) ⟶ ⊤) = 𝟙 _ from rfl, op_id,
    CategoryTheory.Functor.map_id]
  simp only [CommRingCat.hom_ofHom, CommRingCat.id_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe]
  exact DualNumber.scale_mapRingHom _ c a

end Scheme

end AlgebraicGeometry
