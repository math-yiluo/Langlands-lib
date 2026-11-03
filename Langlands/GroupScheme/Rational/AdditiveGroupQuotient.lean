import Langlands.GroupScheme.Rational.AdditivePolynomial
import Langlands.GroupScheme.Rational.SplitUnipotentTransport
import Langlands.GroupScheme.HomDescent
import Langlands.GroupScheme.Dynamic.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Fpqc quotients of a one-dimensional vector group over a field -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry Opposite Polynomial
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

namespace AdditiveGroupQuotient

variable {k : Type u} [Field k]

/-- The `k`-algebra structure of the global functions of a scheme over `Spec k`. -/
def structureMap (T : Over (Spec (CommRingCat.of k))) : k →+* Γ(T.left, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ T.hom.appTop).hom

theorem structureMap_comp {T T' : Over (Spec (CommRingCat.of k))} (b : T' ⟶ T) :
    b.left.appTop.hom.comp (structureMap T) = structureMap T' := by
  rw [structureMap, structureMap, ← CommRingCat.hom_comp, Category.assoc,
    ← Scheme.Hom.comp_appTop, Over.w]

section Coordinates

variable {V : GroupScheme (Spec (CommRingCat.of k))}
  (e : ∀ T : Over (Spec (CommRingCat.of k)),
    (T ⟶ V.X) ≃* Multiplicative (Fin 1 → Γ(T.left, ⊤)))
  (he : ∀ (T T' : Over (Spec (CommRingCat.of k))) (b : T' ⟶ T) (x : T ⟶ V.X),
    (e T' (b ≫ x)).toAdd = fun j => b.left.appTop ((e T x).toAdd j))

/-- The coordinate of a point of a one-dimensional vector group. -/
def coord {T : Over (Spec (CommRingCat.of k))} (x : T ⟶ V.X) : Γ(T.left, ⊤) :=
  (e T x).toAdd 0

/-- The point of a one-dimensional vector group with a given coordinate. -/
def ofCoord {T : Over (Spec (CommRingCat.of k))} (a : Γ(T.left, ⊤)) : T ⟶ V.X :=
  (e T).symm (Multiplicative.ofAdd fun _ => a)

include he in
theorem coord_comp {T T' : Over (Spec (CommRingCat.of k))} (b : T' ⟶ T) (x : T ⟶ V.X) :
    coord e (b ≫ x) = b.left.appTop.hom (coord e x) :=
  congrFun (he T T' b x) 0

theorem coord_mul {T : Over (Spec (CommRingCat.of k))} (x y : T ⟶ V.X) :
    coord e (x * y) = coord e x + coord e y := by
  rw [coord, coord, coord, map_mul, toAdd_mul, Pi.add_apply]

theorem coord_one {T : Over (Spec (CommRingCat.of k))} : coord e (1 : T ⟶ V.X) = 0 := by
  rw [coord, map_one, toAdd_one, Pi.zero_apply]

theorem coord_ofCoord {T : Over (Spec (CommRingCat.of k))} (a : Γ(T.left, ⊤)) :
    coord e (ofCoord e a : T ⟶ V.X) = a := by
  rw [coord, ofCoord, MulEquiv.apply_symm_apply, toAdd_ofAdd]

theorem coord_injective {T : Over (Spec (CommRingCat.of k))} {x y : T ⟶ V.X}
    (h : coord e x = coord e y) : x = y := by
  apply (e T).injective
  apply Multiplicative.toAdd.injective
  funext j
  rw [Subsingleton.elim j 0]
  exact h

/-- Polynomials in the coordinate, as global functions of the vector group. -/
def coordRingHom : k[X] →+* Γ(V.X.left, ⊤) :=
  eval₂RingHom (structureMap V.X) (coord e (𝟙 V.X))

theorem coordRingHom_apply (p : k[X]) :
    coordRingHom e p = p.eval₂ (structureMap V.X) (coord e (𝟙 V.X)) :=
  rfl

include he in
/-- Pulling back a polynomial function along a point evaluates it at the coordinate. -/
theorem appTop_coordRingHom {T : Over (Spec (CommRingCat.of k))} (x : T ⟶ V.X) (p : k[X]) :
    x.left.appTop.hom (coordRingHom e p) = p.eval₂ (structureMap T) (coord e x) := by
  have h := coord_comp e he x (𝟙 V.X)
  rw [Category.comp_id] at h
  rw [coordRingHom_apply, Polynomial.hom_eval₂, structureMap_comp, ← h]

/-- The coordinate identifies the vector group with the affine line. -/
def lineIso : V.X ≅ AffineLine.scheme (Spec (CommRingCat.of k)) where
  hom := (AffineLine.homEquiv V.X).symm (coord e (𝟙 V.X))
  inv := ofCoord e (AffineLine.coord _)
  hom_inv_id := by
    apply coord_injective e
    rw [coord_comp e he, coord_ofCoord]
    exact (AffineLine.homEquiv V.X).apply_symm_apply _
  inv_hom_id := by
    apply AffineLine.hom_ext
    rw [AffineLine.homEquiv_comp, Equiv.apply_symm_apply]
    change (ofCoord e (AffineLine.coord _)).left.appTop.hom (coord e (𝟙 V.X)) = _
    rw [← coord_comp e he, Category.comp_id, coord_ofCoord, AffineLine.homEquiv_apply]
    simp

instance isIso_lineIso_hom_left : IsIso (lineIso e he).hom.left :=
  (inferInstance : IsIso ((Over.forget _).map (lineIso e he).hom))

include e he in
theorem isAffine : IsAffine V.X.left := by
  have : IsAffine (AffineLine.scheme (Spec (CommRingCat.of k))).left :=
    inferInstanceAs (IsAffine 𝔸(PUnit; Spec (CommRingCat.of k)))
  exact IsAffine.of_isIso (lineIso e he).hom.left

/-- The polynomial functions of the affine line, through `𝔸(PUnit; Spec k) ≅ Spec k[PUnit]`. -/
theorem bijective_eval₂Hom_affineLine :
    Function.Bijective (MvPolynomial.eval₂Hom
      (structureMap (AffineLine.scheme (Spec (CommRingCat.of k))))
      (AffineSpace.coord (Spec (CommRingCat.of k)))) := by
  have h := AffineSpace.SpecIso_hom_appTop (n := PUnit.{u + 1}) (CommRingCat.of k)
  have h' : CommRingCat.ofHom (MvPolynomial.eval₂Hom
      (structureMap (AffineLine.scheme (Spec (CommRingCat.of k))))
      (AffineSpace.coord (Spec (CommRingCat.of k)))) =
      (Scheme.ΓSpecIso _).inv ≫ (AffineSpace.SpecIso PUnit.{u + 1} (CommRingCat.of k)).hom.appTop := by
    rw [h, Iso.inv_hom_id_assoc]
    rfl
  have : IsIso (AffineSpace.SpecIso PUnit.{u + 1} (CommRingCat.of k)).hom.appTop :=
    inferInstanceAs (IsIso ((AffineSpace.SpecIso PUnit.{u + 1} (CommRingCat.of k)).hom.app ⊤))
  have hb : Function.Bijective ((Scheme.ΓSpecIso _).inv ≫
      (AffineSpace.SpecIso PUnit.{u + 1} (CommRingCat.of k)).hom.appTop).hom := by
    rw [CommRingCat.hom_comp, RingHom.coe_comp]
    exact (ConcreteCategory.bijective_of_isIso
      (AffineSpace.SpecIso PUnit.{u + 1} (CommRingCat.of k)).hom.appTop).comp
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).inv)
  rw [← h'] at hb
  exact hb

theorem bijective_eval₂RingHom_affineLine :
    Function.Bijective (eval₂RingHom
      (structureMap (AffineLine.scheme (Spec (CommRingCat.of k))))
      (AffineLine.coord (Spec (CommRingCat.of k)))) := by
  have h : eval₂RingHom (structureMap (AffineLine.scheme (Spec (CommRingCat.of k))))
      (AffineLine.coord (Spec (CommRingCat.of k))) =
      (MvPolynomial.eval₂Hom (structureMap (AffineLine.scheme (Spec (CommRingCat.of k))))
        (AffineSpace.coord (Spec (CommRingCat.of k)))).comp
        (MvPolynomial.uniqueAlgEquiv k PUnit.{u + 1}).symm.toRingEquiv.toRingHom := by
    apply Polynomial.ringHom_ext
    · intro c
      show eval₂ (structureMap (AffineLine.scheme (Spec (CommRingCat.of k))))
          (AffineLine.coord (Spec (CommRingCat.of k))) (C c) =
        MvPolynomial.eval₂Hom (structureMap (AffineLine.scheme (Spec (CommRingCat.of k))))
          (AffineSpace.coord (Spec (CommRingCat.of k)))
          ((MvPolynomial.uniqueAlgEquiv k PUnit.{u + 1}).symm (C c))
      rw [eval₂_C, MvPolynomial.uniqueAlgEquiv_symm_apply, eval₂_C]
      exact (MvPolynomial.eval₂Hom_C (structureMap (AffineLine.scheme (Spec (CommRingCat.of k))))
        (AffineSpace.coord (Spec (CommRingCat.of k))) c).symm
    · show eval₂ (structureMap (AffineLine.scheme (Spec (CommRingCat.of k))))
          (AffineLine.coord (Spec (CommRingCat.of k))) X =
        MvPolynomial.eval₂Hom (structureMap (AffineLine.scheme (Spec (CommRingCat.of k))))
          (AffineSpace.coord (Spec (CommRingCat.of k)))
          ((MvPolynomial.uniqueAlgEquiv k PUnit.{u + 1}).symm X)
      rw [eval₂_X, MvPolynomial.uniqueAlgEquiv_symm_apply, eval₂_X]
      exact (MvPolynomial.eval₂Hom_X' (structureMap (AffineLine.scheme (Spec (CommRingCat.of k))))
        (AffineSpace.coord (Spec (CommRingCat.of k))) PUnit.unit).symm
  rw [h]
  exact bijective_eval₂Hom_affineLine.comp (RingEquiv.bijective _)

include he in
theorem coordRingHom_bijective : Function.Bijective (coordRingHom e) := by
  have h : coordRingHom e = (lineIso e he).hom.left.appTop.hom.comp
      (eval₂RingHom (structureMap (AffineLine.scheme (Spec (CommRingCat.of k))))
        (AffineLine.coord (Spec (CommRingCat.of k)))) := by
    apply Polynomial.ringHom_ext
    · intro c
      rw [RingHom.comp_apply, coe_eval₂RingHom, eval₂_C, coordRingHom_apply, eval₂_C,
        ← structureMap_comp (lineIso e he).hom, RingHom.comp_apply]
    · rw [RingHom.comp_apply, coe_eval₂RingHom, eval₂_X, coordRingHom_apply, eval₂_X]
      exact ((AffineLine.homEquiv V.X).apply_symm_apply _).symm
  have : IsIso (lineIso e he).hom.left.appTop :=
    inferInstanceAs (IsIso ((lineIso e he).hom.left.app ⊤))
  rw [h]
  exact (ConcreteCategory.bijective_of_isIso (lineIso e he).hom.left.appTop).comp
    bijective_eval₂RingHom_affineLine

/-- The coordinate ring of a one-dimensional vector group is the polynomial ring. -/
def coordEquiv : k[X] ≃+* Γ(V.X.left, ⊤) :=
  RingEquiv.ofBijective (coordRingHom e) (coordRingHom_bijective e he)

/-- The endomorphism of the vector group given by a polynomial in the coordinate. -/
def polyEndo (g : k[X]) : V.X ⟶ V.X :=
  ofCoord e (coordRingHom e g)

include he in
theorem coord_comp_polyEndo {T : Over (Spec (CommRingCat.of k))} (x : T ⟶ V.X) (g : k[X]) :
    coord e (x ≫ polyEndo e g) = g.eval₂ (structureMap T) (coord e x) := by
  rw [coord_comp e he, polyEndo, coord_ofCoord, appTop_coordRingHom e he]

include he in
theorem comp_polyEndo_eq_one_iff {T : Over (Spec (CommRingCat.of k))} (x : T ⟶ V.X)
    (g : k[X]) : x ≫ polyEndo e g = 1 ↔ g.eval₂ (structureMap T) (coord e x) = 0 := by
  rw [← coord_comp_polyEndo e he]
  exact ⟨fun h => by rw [h, coord_one], fun h => coord_injective e (by rw [h, coord_one])⟩

include he in
/-- A polynomial that is additive on the functions of every test scheme is an endomorphism of
the group. -/
theorem isMonHom_polyEndo {g : k[X]}
    (hadd : ∀ (T : Over (Spec (CommRingCat.of k))) (a b : Γ(T.left, ⊤)),
      g.eval₂ (structureMap T) (a + b) =
        g.eval₂ (structureMap T) a + g.eval₂ (structureMap T) b) :
    IsMonHom (polyEndo e g) where
  one_hom := by
    apply coord_injective e
    rw [MonObj.one_eq_one, coord_comp_polyEndo e he, coord_one]
    have h := hadd (𝟙_ _) 0 0
    rw [add_zero] at h
    linear_combination -h
  mul_hom := by
    apply coord_injective e
    rw [MonObj.mul_eq_mul, coord_comp_polyEndo e he, coord_mul, hadd, MonObj.comp_mul, coord_mul,
      tensorHom_fst, tensorHom_snd, coord_comp_polyEndo e he, coord_comp_polyEndo e he]

include he in
theorem appTop_polyEndo_comp (g : k[X]) :
    (polyEndo e g).left.appTop.hom.comp (coordRingHom e) =
      (coordRingHom e).comp (AdditivePolynomial.compHom g) := by
  apply Polynomial.ringHom_ext
  · intro c
    rw [RingHom.comp_apply, RingHom.comp_apply, appTop_coordRingHom e he, eval₂_C,
      AdditivePolynomial.compHom_C, coordRingHom_apply, eval₂_C]
  · rw [RingHom.comp_apply, RingHom.comp_apply, appTop_coordRingHom e he, eval₂_X,
      AdditivePolynomial.compHom_X, polyEndo, coord_ofCoord]

include he in
theorem appTop_polyEndo (g : k[X]) :
    (polyEndo e g).left.appTop.hom = (coordEquiv e he).toRingHom.comp
      ((AdditivePolynomial.compHom g).comp (coordEquiv e he).symm.toRingHom) := by
  ext r
  obtain ⟨p, rfl⟩ := (coordEquiv e he).surjective r
  have h := congrArg (fun φ => φ p) (appTop_polyEndo_comp e he g)
  simp only [RingHom.comp_apply] at h
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    RingEquiv.symm_apply_apply]
  exact h

end Coordinates

section Kernel

variable {V Q : GroupScheme (Spec (CommRingCat.of k))}
  (e : ∀ T : Over (Spec (CommRingCat.of k)),
    (T ⟶ V.X) ≃* Multiplicative (Fin 1 → Γ(T.left, ⊤)))
  (he : ∀ (T T' : Over (Spec (CommRingCat.of k))) (b : T' ⟶ T) (x : T ⟶ V.X),
    (e T' (b ≫ x)).toAdd = fun j => b.left.appTop ((e T x).toAdd j))
  (q : V ⟶ Q)

/-- The ideal of the scheme kernel of `q`, as an ideal of polynomials in the coordinate. -/
def kernelIdeal : Ideal k[X] :=
  (RingHom.ker (kernelι q).hom.hom.left.appTop.hom).comap (coordRingHom e)

/-- The monic, or zero, generator of the kernel ideal. -/
def kernelPolynomial : k[X] :=
  Submodule.IsPrincipal.generator (kernelIdeal e q) *
    C (Submodule.IsPrincipal.generator (kernelIdeal e q)).leadingCoeff⁻¹

theorem kernelIdeal_eq_span : kernelIdeal e q = Ideal.span {kernelPolynomial e q} := by
  conv_lhs => rw [← Ideal.span_singleton_generator (kernelIdeal e q)]
  by_cases h : Submodule.IsPrincipal.generator (kernelIdeal e q) = 0
  · rw [kernelPolynomial, h, zero_mul]
  · rw [kernelPolynomial, Ideal.span_singleton_mul_right_unit]
    exact isUnit_C.mpr (inv_ne_zero (leadingCoeff_ne_zero.mpr h)).isUnit

theorem kernelPolynomial_monic (h : kernelPolynomial e q ≠ 0) : (kernelPolynomial e q).Monic := by
  have h' : Submodule.IsPrincipal.generator (kernelIdeal e q) ≠ 0 := by
    intro h0
    apply h
    rw [kernelPolynomial, h0, zero_mul]
  exact monic_mul_leadingCoeff_inv h'

include he in
theorem ker_appTop_kernelι_eq :
    RingHom.ker (kernelι q).hom.hom.left.appTop.hom =
      Ideal.span {coordRingHom e (kernelPolynomial e q)} := by
  rw [← Ideal.map_comap_of_surjective _ (coordRingHom_bijective e he).2
    (RingHom.ker (kernelι q).hom.hom.left.appTop.hom)]
  change Ideal.map (coordRingHom e) (kernelIdeal e q) = _
  rw [kernelIdeal_eq_span, Ideal.map_span, Set.image_singleton]

include he in
/-- A point lies in the kernel of `q` exactly when the kernel polynomial vanishes at its
coordinate. -/
theorem mem_range_kernelι_iff_eval [IsSeparated Q.X.hom] {T : Over (Spec (CommRingCat.of k))}
    (x : T ⟶ V.X) :
    x ∈ (SubgroupFunctor.range (kernelι q)).carrier T ↔
      (kernelPolynomial e q).eval₂ (structureMap T) (coord e x) = 0 := by
  have : IsAffine V.X.left := isAffine e he
  have hI := ker_appTop_kernelι_eq e he q
  rw [← appTop_coordRingHom e he x]
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    have hmem : coordRingHom e (kernelPolynomial e q) ∈
        RingHom.ker (kernelι q).hom.hom.left.appTop.hom := by
      rw [hI]
      exact Ideal.subset_span rfl
    rw [Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply,
      RingHom.mem_ker.mp hmem, map_zero]
  · intro h
    have hle : RingHom.ker (kernelι q).hom.hom.left.appTop.hom ≤
        RingHom.ker x.left.appTop.hom := by
      rw [hI, Ideal.span_le, Set.singleton_subset_iff]
      exact h
    have hker : (kernelι q).hom.hom.left.ker ≤ x.left.ker := by
      rw [Scheme.ker_of_isAffine, Scheme.ker_of_isAffine]
      exact (map_le_map_iff (Scheme.IdealSheafData.equivOfIsAffine (X := V.X.left)).symm).mpr hle
    let a := IsClosedImmersion.lift (kernelι q).hom.hom.left x.left hker
    have ha : a ≫ (kernelι q).hom.hom.left = x.left := IsClosedImmersion.lift_fac _ _ _
    refine SubgroupFunctor.mem_range.mpr ⟨Over.homMk a ?_, Over.OverMorphism.ext ha⟩
    rw [← Over.w (kernelι q).hom.hom, ← Category.assoc, ha, Over.w]

include he in
theorem eval₂_add_eq_zero [IsSeparated Q.X.hom] {T : Over (Spec (CommRingCat.of k))}
    {a b : Γ(T.left, ⊤)} (ha : (kernelPolynomial e q).eval₂ (structureMap T) a = 0)
    (hb : (kernelPolynomial e q).eval₂ (structureMap T) b = 0) :
    (kernelPolynomial e q).eval₂ (structureMap T) (a + b) = 0 := by
  have ha' : (ofCoord e a : T ⟶ V.X) ∈ (SubgroupFunctor.range (kernelι q)).carrier T :=
    (mem_range_kernelι_iff_eval e he q _).mpr (by rwa [coord_ofCoord])
  have hb' : (ofCoord e b : T ⟶ V.X) ∈ (SubgroupFunctor.range (kernelι q)).carrier T :=
    (mem_range_kernelι_iff_eval e he q _).mpr (by rwa [coord_ofCoord])
  have hab := (mem_range_kernelι_iff_eval e he q _).mp (Subgroup.mul_mem _ ha' hb')
  rwa [coord_mul, coord_ofCoord, coord_ofCoord] at hab

include he in
/-- The universal pair of roots of the kernel polynomial: `f(X + Y)` lies in `(f(X), f(Y))`. -/
theorem taylor_mem_span [IsSeparated Q.X.hom] :
    taylor (X : k[X]) ((kernelPolynomial e q).map C) ∈
      Ideal.span {C (kernelPolynomial e q), (kernelPolynomial e q).map C} := by
  set f := kernelPolynomial e q
  set I : Ideal k[X][X] := Ideal.span {C f, f.map C}
  let ρR : k →+* k[X][X] ⧸ I := (Ideal.Quotient.mk I).comp ((C : k[X] →+* k[X][X]).comp C)
  let T : Over (Spec (CommRingCat.of k)) :=
    Over.mk (Spec.map (CommRingCat.ofHom ρR : CommRingCat.of k ⟶ CommRingCat.of (k[X][X] ⧸ I)))
  let γ : k[X][X] ⧸ I →+* Γ(T.left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of (k[X][X] ⧸ I))).inv.hom
  have hγ : Function.Injective γ :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (k[X][X] ⧸ I))).inv).1
  have hρ : structureMap T = (γ.comp (Ideal.Quotient.mk I)).comp
      ((C : k[X] →+* k[X][X]).comp C) := by
    change ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
      (Spec.map (CommRingCat.ofHom ρR :
        CommRingCat.of k ⟶ CommRingCat.of (k[X][X] ⧸ I))).appTop).hom = _
    rw [← Scheme.ΓSpecIso_inv_naturality]
    rfl
  have hev : ∀ y : k[X][X], f.eval₂ (structureMap T) (γ (Ideal.Quotient.mk I y)) =
      γ (Ideal.Quotient.mk I (f.eval₂ ((C : k[X] →+* k[X][X]).comp C) y)) := by
    intro y
    rw [hρ]
    exact (Polynomial.hom_eval₂ f _ (γ.comp (Ideal.Quotient.mk I)) y).symm
  have hX : f.eval₂ ((C : k[X] →+* k[X][X]).comp C) X = f.map C := by
    rw [← eval₂_map, eval₂_C_X]
  have hCX : f.eval₂ ((C : k[X] →+* k[X][X]).comp C) (C X) = C f := by
    rw [← Polynomial.hom_eval₂, eval₂_C_X]
  have ha : f.eval₂ (structureMap T) (γ (Ideal.Quotient.mk I X)) = 0 := by
    rw [hev, hX, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp)), map_zero]
  have hb : f.eval₂ (structureMap T) (γ (Ideal.Quotient.mk I (C X))) = 0 := by
    rw [hev, hCX, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp)), map_zero]
  have hab := eval₂_add_eq_zero e he q ha hb
  rw [← map_add, ← map_add, hev, map_eq_zero_iff γ hγ] at hab
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← hab, taylor_apply]
  congr 1
  change (f.map C).eval₂ C (X + C X) = _
  rw [eval₂_map]

end Kernel

/-- The scheme kernel of a homomorphism maps trivially. -/
theorem kernelι_comp_self {B : Scheme.{u}} {G H : GroupScheme B} (g : G ⟶ H) :
    kernelι g ≫ g = 0 := by
  apply Grp.hom_ext
  change (kernelι g).hom.hom ≫ g.hom.hom = 1
  exact (mem_range_kernelι_iff g _).mp (SubgroupFunctor.mem_range.mpr ⟨𝟙 _, Category.id_comp _⟩)

end AdditiveGroupQuotient

open AdditiveGroupQuotient AdditivePolynomial in
/-- A quotient of a one-dimensional vector group over a field, by a flat surjective
homomorphism to a separated group scheme, is trivial or again a one-dimensional vector group.
The kernel is cut out by an additive polynomial `f`, and the quotient is identified with the
endomorphism `x ↦ f(x)` through fpqc homomorphism descent in both directions. -/
theorem trivial_or_isVectorGroup_of_flat_surjective {k : Type u} [Field k]
    {V Q : GroupScheme (Spec (CommRingCat.of k))} (hV : IsVectorGroupOfDimension V 1)
    (q : V ⟶ Q) [IsSeparated Q.X.hom] [Flat q.hom.hom.left] [Surjective q.hom.hom.left] :
    HasSplitSeries 0 Q ∨ IsVectorGroupOfDimension Q 1 := by
  obtain ⟨e, he⟩ := hV
  have : IsAffine V.X.left := isAffine e he
  have : QuasiCompact (q.hom.hom.left ≫ Q.X.hom) := by
    rw [Over.w]
    infer_instance
  have : QuasiCompact q.hom.hom.left := QuasiCompact.of_comp _ Q.X.hom
  have hk := kernelι_comp_self q
  by_cases hf0 : kernelPolynomial e q = 0
  · left
    have hq1 : q.hom.hom = 1 := by
      have h := (mem_range_kernelι_iff_eval e he q (𝟙 V.X)).mpr (by rw [hf0, eval₂_zero])
      rw [mem_range_kernelι_iff, Category.id_comp] at h
      exact h
    have h1 : 𝟙 Q = 0 := by
      have hd0 := FpqcHomDescent.unique q q hk 0 (by
        apply Grp.hom_ext
        change q.hom.hom ≫ 1 = q.hom.hom
        rw [MonObj.comp_one, hq1])
      rw [FpqcHomDescent.unique q q hk (𝟙 Q) (Category.comp_id q), hd0]
    refine SubgroupFunctor.ext fun T => ?_
    rw [SubgroupFunctor.bot_carrier, eq_bot_iff]
    intro y hy
    obtain ⟨z, rfl⟩ := SubgroupFunctor.mem_range.mp hy
    rw [Subgroup.mem_bot, h1]
    exact MonObj.comp_one z
  · right
    set f := kernelPolynomial e q with hf
    have hmonic : f.Monic := kernelPolynomial_monic e q hf0
    have hd : 0 < f.natDegree := by
      rw [Nat.pos_iff_ne_zero]
      intro hdeg
      have h1 := eq_one_of_monic_natDegree_zero hmonic hdeg
      have h := (mem_range_kernelι_iff_eval e he q (1 : V.X ⟶ V.X)).mp (Subgroup.one_mem _)
      rw [← hf, h1, eval₂_one] at h
      apply one_ne_zero (α := k[X])
      apply (coordRingHom_bijective e he).1
      rw [map_one, map_zero]
      exact h
    have htaylor := taylor_eq_of_mem_span hmonic hd (taylor_mem_span e he q)
    have : IsMonHom (polyEndo e f) :=
      isMonHom_polyEndo e he fun T a b => eval₂_add_of_taylor_eq htaylor _ a b
    let φ : V ⟶ V := Grp.homMk (polyEndo e f)
    have hff : (polyEndo e f).left.appTop.hom.FaithfullyFlat := by
      rw [appTop_polyEndo e he]
      exact RingHom.FaithfullyFlat.respectsIso.1 _ _
        (RingHom.FaithfullyFlat.respectsIso.2 _ _ (compHom_faithfullyFlat hmonic hd))
    obtain ⟨hflat, hsurj⟩ :=
      (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine (polyEndo e f).left).mpr hff
    have : Flat φ.hom.hom.left := hflat
    have : Surjective φ.hom.hom.left := hsurj
    have hmem : ∀ {T : Over (Spec (CommRingCat.of k))} (x : T ⟶ V.X),
        x ∈ (SubgroupFunctor.range (kernelι q)).carrier T ↔ x ≫ φ.hom.hom = 1 := by
      intro T x
      rw [mem_range_kernelι_iff_eval e he q]
      exact (comp_polyEndo_eq_one_iff e he x f).symm
    have hk1 : kernelι q ≫ φ = 0 := by
      apply Grp.hom_ext
      change (kernelι q).hom.hom ≫ φ.hom.hom = 1
      exact (hmem _).mp (SubgroupFunctor.mem_range.mpr ⟨𝟙 _, Category.id_comp _⟩)
    have hk2 : kernelι φ ≫ q = 0 := by
      apply Grp.hom_ext
      change (kernelι φ).hom.hom ≫ q.hom.hom = 1
      rw [← mem_range_kernelι_iff, hmem, ← mem_range_kernelι_iff]
      exact SubgroupFunctor.mem_range.mpr ⟨𝟙 _, Category.id_comp _⟩
    have hkφ := kernelι_comp_self φ
    have hq' : q ≫ FpqcHomDescent.hom q φ hk1 = φ := FpqcHomDescent.fac q φ hk1
    have hφ : φ ≫ FpqcHomDescent.hom φ q hk2 = q := FpqcHomDescent.fac φ q hk2
    have hαβ : FpqcHomDescent.hom q φ hk1 ≫ FpqcHomDescent.hom φ q hk2 = 𝟙 Q := by
      exact (FpqcHomDescent.unique q q hk _ (by rw [← Category.assoc, hq', hφ])).trans
        (FpqcHomDescent.unique q q hk (𝟙 Q) (Category.comp_id q)).symm
    have hβα : FpqcHomDescent.hom φ q hk2 ≫ FpqcHomDescent.hom q φ hk1 = 𝟙 V := by
      exact (FpqcHomDescent.unique φ φ hkφ _ (by rw [← Category.assoc, hφ, hq'])).trans
        (FpqcHomDescent.unique φ φ hkφ (𝟙 V) (Category.comp_id φ)).symm
    exact IsVectorGroupOfDimension.of_iso ⟨_, _, hβα, hαβ⟩ ⟨e, he⟩

/-- The fppf-quotient form: an fppf quotient of a one-dimensional vector group over a field,
with separated target, has a split series of length zero or is a one-dimensional vector
group. -/
theorem trivial_or_isVectorGroup_of_isFppfQuotient {k : Type u} [Field k]
    {V Q : GroupScheme (Spec (CommRingCat.of k))} (hV : IsVectorGroupOfDimension V 1)
    {N : SubgroupFunctor V} (q : V ⟶ Q) [IsSeparated Q.X.hom] (hq : IsFppfQuotient N q) :
    HasSplitSeries 0 Q ∨ IsVectorGroupOfDimension Q 1 := by
  have : Flat q.hom.hom.left := hq.1
  have : Surjective q.hom.hom.left := hq.2.1
  exact trivial_or_isVectorGroup_of_flat_surjective hV q

end Langlands.GroupScheme.RelativeRoot
