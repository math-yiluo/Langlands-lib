/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import WeilConjectures.AlgebraicGeometry.DensePoints
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.PropertyC
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.Mathlib.AlgebraicGeometry.ResidueField
import WeilConjectures.AlgebraicGeometry.SmoothSectionComponentOpen

/-!
# Slicing a smooth morphism

A smooth morphism `f : X ⟶ S` becomes, after an étale covering of `X`, a smooth morphism of
affine schemes with geometrically connected fibres and a section, over a scheme étale over `S`
(Stacks `0EY4`).

The proof follows Stacks. In each fibre of `f` the closed points with finite separable residue
field are dense (Stacks `056U`), and through each of them passes an étale slice `ι : Z ⟶ X`,
that is, `ι ≫ f` is étale (Stacks `057G`). The base change `X ×_S Z ⟶ Z` then has a section,
whose relative connected component is open with geometrically irreducible fibres (Stacks `055R`).
The projection to `X` maps connected components of fibres onto connected components, so these
relative components cover `X`. A second slicing after shrinking to an affine open makes all the
schemes affine.

## Main statements

- `AlgebraicGeometry.Smooth.exists_mem_etale_residueFieldMap`: in every fibre of a smooth
  morphism, the points with finite separable residue field extension are dense.
- `AlgebraicGeometry.AffineSpace.exists_etale_comp_of_etale_residueFieldMap`: étale slices of
  affine space.
- `AlgebraicGeometry.Smooth.exists_etale_comp_of_etale_residueFieldMap`: through a point with
  finite separable residue field extension passes an étale slice.
- `AlgebraicGeometry.Smooth.exists_geometricallyIrreducible_of_section`: the relative connected
  component of a section of a smooth morphism is open, with geometrically irreducible fibres.
- `AlgebraicGeometry.Smooth.exists_etale_factorization_of_mem`: the slicing near one point.
- `AlgebraicGeometry.Smooth.exists_etaleCover_factorization`: the slicing of a smooth morphism.

## References

- Stacks Project, Tag `0EY4`, <https://stacks.math.columbia.edu/tag/0EY4>
- Stacks Project, Tags `056U`, `057G`, `055R`, `04KV`
-/

@[expose] public section

universe u

open CategoryTheory Limits MvPolynomial

namespace AlgebraicGeometry

/-- A point of the fibre of `f` over `s` whose residue field is finite separable over `κ(s)`
maps to a point of `X` whose residue field is finite separable over `κ(s)`. -/
lemma Scheme.Hom.etale_residueFieldMap_fiberι {X S : Scheme.{u}} (f : X ⟶ S) {s : S}
    (y : f.fiber s) (hy : ((f.fiberToSpecResidueField s).residueFieldAlgebraMap y).Etale) :
    (f.residueFieldMap (f.fiberι s y)).hom.Etale := by
  have h : f (f.fiberι s y) = s := by
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.fiber_fac, Scheme.Hom.comp_apply,
      Scheme.fromSpecResidueField_apply]
  let a := (f.fiberToSpecResidueField s).residueFieldAlgebraMap y
  let e := (S.residueFieldCongr h.symm).hom
  let b := f.residueFieldMap (f.fiberι s y)
  let c := (f.fiberι s).residueFieldMap y
  have hac : a = (e ≫ b ≫ c).hom := by
    have h1 : Spec.map (CommRingCat.ofHom a) ≫ S.fromSpecResidueField s =
        (f.fiber s).fromSpecResidueField y ≫ f.fiberToSpecResidueField s ≫
          S.fromSpecResidueField s :=
      (congrArg (· ≫ S.fromSpecResidueField s)
        ((f.fiberToSpecResidueField s).specMap_residueFieldAlgebraMap y)).trans
        (Category.assoc _ _ _)
    have h2 : Spec.map (e ≫ b ≫ c) ≫ S.fromSpecResidueField s =
        (f.fiber s).fromSpecResidueField y ≫ f.fiberToSpecResidueField s ≫
          S.fromSpecResidueField s := by
      rw [Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
        S.residueFieldCongr_fromSpecResidueField h.symm,
        Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
        Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField_assoc, Scheme.Hom.fiber_fac]
    exact congrArg CommRingCat.Hom.hom
      (Spec.map_injective ((cancel_mono (S.fromSpecResidueField s)).mp (h1.trans h2.symm)))
  -- the residue field of `f.fiberι s y` is finite separable over `κ(s)`
  have key : (e ≫ b).hom.Etale := by
    refine RingHom.Etale.of_comp_of_field (e ≫ b).hom c.hom ?_
    rw [← CommRingCat.hom_comp, Category.assoc, ← hac]
    exact hy
  have hb : b.hom = (e ≫ b).hom.comp
      (S.residueFieldCongr h).commRingCatIsoToRingEquiv.toRingHom := by
    ext r
    change b.hom r = b.hom (((S.residueFieldCongr h).hom ≫ (S.residueFieldCongr h).inv).hom r)
    rw [Iso.hom_inv_id]
    rfl
  change b.hom.Etale
  rw [hb]
  exact RingHom.Etale.respectsIso.2 _ _ key

/-- **Density of separable points** (Stacks `056U`). Let `f : X ⟶ S` be smooth. Every open
`U` of `X` meeting the fibre through `x` contains a point `x'` of that fibre whose residue field
is finite separable over `κ(f x)`, that is, `κ(f x) ⟶ κ(x')` is étale. -/
@[stacks 056U]
theorem Smooth.exists_mem_etale_residueFieldMap {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f]
    (U : X.Opens) {x : X} (hx : x ∈ U) :
    ∃ x' ∈ U, f x' = f x ∧ (f.residueFieldMap x').hom.Etale := by
  have : Smooth (f.fiberToSpecResidueField (f x)) := inferInstanceAs (Smooth (pullback.snd _ _))
  have hd := @Scheme.Hom.dense_setOf_isClosed_finite_isSeparable _
    (IsLocalRing.ResidueField (S.presheaf.stalk (f x))) _ (f.fiberToSpecResidueField (f x)) this
  obtain ⟨y, hyU, -, hy⟩ := hd.inter_open_nonempty
      (f.fiberι (f x) ⁻¹ᵁ U) (f.fiberι (f x) ⁻¹ᵁ U).2
      ⟨f.asFiber x, by simpa [Scheme.Hom.fiberι_asFiber] using hx⟩
  refine ⟨f.fiberι _ y, hyU, ?_, f.etale_residueFieldMap_fiberι y ?_⟩
  · rw [← Scheme.Hom.comp_apply, Scheme.Hom.fiber_fac, Scheme.Hom.comp_apply,
      Scheme.fromSpecResidueField_apply]
  · let _ := ((f.fiberToSpecResidueField (f x)).residueFieldAlgebraMap y).toAlgebra
    obtain ⟨_, _⟩ := hy
    exact RingHom.etale_algebraMap.mpr .of_finite_of_isSeparable

/-- Let `w` be a point of the affine space `𝔸(n; U)` over an affine scheme `U`, `n` finite, whose
residue field is finite separable over that of its image in `U`. Then some affine scheme `Z`,
étale over `U`, maps to `𝔸(n; U)` over `U` with `w` in its image. -/
theorem AffineSpace.exists_etale_comp_of_etale_residueFieldMap {n : Type u} [Finite n]
    {U : Scheme.{u}} [IsAffine U] (w : 𝔸(n; U))
    (hw : ((𝔸(n; U) ↘ U).residueFieldMap w).hom.Etale) :
    ∃ (Z : Scheme.{u}) (ι : Z ⟶ 𝔸(n; U)) (z : Z), IsAffine Z ∧ Etale (ι ≫ (𝔸(n; U) ↘ U)) ∧
      ι z = w := by
  set iso := AffineSpace.isoOfIsAffine n U
  let φ : CommRingCat.of Γ(U, ⊤) ⟶ CommRingCat.of (MvPolynomial n Γ(U, ⊤)) :=
    CommRingCat.ofHom C
  have hE : 𝔸(n; U) ↘ U = iso.hom ≫ Spec.map φ ≫ U.isoSpec.inv := by
    rw [← AffineSpace.isoOfIsAffine_inv_over, Iso.hom_inv_id_assoc]
  set q := iso.hom w
  have : q.asIdeal.IsPrime := q.2
  have hq : ((Spec.map φ).residueFieldMap q).hom.Etale := by
    rw [Scheme.Hom.etale_residueFieldMap_congr hE,
      Scheme.Hom.etale_residueFieldMap_comp_iff_left,
      Scheme.Hom.etale_residueFieldMap_comp_iff_right] at hw
    exact hw
  have : ((Spec.map φ) q).asIdeal.IsPrime := ((Spec.map φ) q).2
  have h := Spec.residueFieldMap_residueFieldIso_hom φ q
  have h' := (RingHom.Etale.respectsIso.cancel_right_isIso _
    (Scheme.Spec.residueFieldIso _ q).hom).mpr hq
  rw [← CommRingCat.hom_comp, h, CommRingCat.hom_comp,
    RingHom.Etale.respectsIso.cancel_left_isIso] at h'
  obtain ⟨B, _, _, _, ψ, Q, _, hQ⟩ := MvPolynomial.exists_etale_comap_eq q.asIdeal _ _ h'
  refine ⟨Spec (.of B), Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ iso.inv, ⟨Q, ‹_›⟩,
    inferInstance, ?_, ?_⟩
  · have hψ : CommRingCat.ofHom C ≫ CommRingCat.ofHom ψ.toRingHom =
        CommRingCat.ofHom (algebraMap Γ(U, ⊤) B) := by
      ext r
      exact ψ.commutes r
    have : Etale (Spec.map (CommRingCat.ofHom (algebraMap Γ(U, ⊤) B))) :=
      HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr inferInstance)
    rw [Category.assoc, AffineSpace.isoOfIsAffine_inv_over, ← Category.assoc, ← Spec.map_comp,
      hψ]
    infer_instance
  · have hz : Spec.map (CommRingCat.ofHom ψ.toRingHom) ⟨Q, ‹_›⟩ = q := PrimeSpectrum.ext hQ
    change iso.inv (Spec.map (CommRingCat.ofHom ψ.toRingHom) ⟨Q, ‹_›⟩) = w
    rw [hz]
    change (iso.hom ≫ iso.inv) w = w
    simp

/-- **Étale slices** (Stacks `057G`). Let `f: X ⟶ S` be smooth and let `x: X` have finite
separable residue field over `κ(f x)`, so that `x` is a closed point of its fibre. Then there is
an affine scheme `Z`, a point `z: Z` and a morphism `ι: Z ⟶ X` through `x` such that `ι ≫ f`
is étale. -/
@[stacks 057G]
theorem Smooth.exists_etale_comp_of_etale_residueFieldMap {X S : Scheme.{u}} (f : X ⟶ S)
    [Smooth f] {x : X} (hx : (f.residueFieldMap x).hom.Etale) :
    ∃ (Z : Scheme.{u}) (ι : Z ⟶ X) (z : Z), IsAffine Z ∧ Etale (ι ≫ f) ∧ ι z = x := by
  obtain ⟨d, U, V, hU, hV, -, hxV, hVU, e, he, hge⟩ :=
    f.exists_etale_to_affineSpace_of_mem_smoothLocus (x := x)
      (by rw [f.smoothLocus_eq_top]; trivial)
  have : IsAffine U := hU
  have : IsAffine V := hV
  let x₀ : V.toScheme := ⟨x, hxV⟩
  set π := 𝔸(ULift.{u} (Fin d); U.toScheme) ↘ U.toScheme
  -- the residue field of `x₀` is finite separable over that of its image in `U`
  have h0 : ((f.resLE U V hVU).residueFieldMap x₀).hom.Etale := by
    rw [← Scheme.Hom.etale_residueFieldMap_comp_iff_right _ U.ι,
      Scheme.Hom.etale_residueFieldMap_congr (Scheme.Hom.resLE_comp_ι f hVU),
      Scheme.Hom.etale_residueFieldMap_comp_iff_left]
    exact hx
  rw [← hge, Scheme.residueFieldMap_comp] at h0
  have hw := RingHom.Etale.of_comp_of_field (π.residueFieldMap (e x₀)).hom
    (e.residueFieldMap x₀).hom h0
  obtain ⟨Z₀, ι₀, z₀, hZ₀, hι₀, hz₀⟩ :=
    AffineSpace.exists_etale_comp_of_etale_residueFieldMap _ hw
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := e) (g := ι₀) x₀ z₀ hz₀.symm
  refine ⟨pullback e ι₀, pullback.fst e ι₀ ≫ V.ι, z, inferInstance, ?_, by simp [hz, x₀]⟩
  have : pullback.fst e ι₀ ≫ V.ι ≫ f = pullback.snd e ι₀ ≫ (ι₀ ≫ π) ≫ U.ι := by
    rw [← Scheme.Hom.resLE_comp_ι f hVU, ← hge]
    simp only [Category.assoc]
    rw [pullback.condition_assoc]
  rw [Category.assoc, this]
  infer_instance

/-- **The relative connected component of a section** (Stacks `055R`). Let `g : P ⟶ T` be
smooth, quasi-compact and quasi-separated, with a section `σ`. Then there is an open `U` of `P`
containing the image of `σ` and every point `p` lying in the connected component of `σ (g p)` in
its fibre, such that `U ⟶ T` has geometrically irreducible fibres. -/
@[stacks 055R]
theorem Smooth.exists_geometricallyIrreducible_of_section {P T : Scheme.{u}} (g : P ⟶ T)
    [Smooth g] [QuasiCompact g] [QuasiSeparated g] (σ : T ⟶ P) (hσ : σ ≫ g = 𝟙 T) :
    ∃ U : P.Opens, Set.range σ ⊆ U ∧ GeometricallyIrreducible (U.ι ≫ g) ∧
      ∀ p : P, p ∈ connectedComponentIn (g ⁻¹' {g p}) (σ (g p)) → p ∈ U := by
  let U : P.Opens := ⟨{p : P | p ∈ connectedComponentIn (g ⁻¹' {g p}) (σ (g p))},
    Smooth.isOpen_section_component g σ hσ⟩
  have hsec (t : T) : g (σ t) = t := by
    change (σ ≫ g) t = t
    rw [hσ]
    rfl
  have hσU : Set.range σ ⊆ U := by
    rintro _ ⟨t, rfl⟩
    change σ t ∈ connectedComponentIn (g ⁻¹' {g (σ t)}) (σ (g (σ t)))
    rw [hsec]
    exact mem_connectedComponentIn (hsec t)
  let h := U.ι ≫ g
  let τ : T ⟶ U.toScheme := IsOpenImmersion.lift U.ι σ (by simpa using hσU)
  have hτ : τ ≫ h = 𝟙 T := by
    dsimp [h, τ]
    rw [← Category.assoc, IsOpenImmersion.lift_fac, hσ]
  have hconnected (t : T) : ConnectedSpace (h.fiber t) := by
    let j := h.fiberι t ≫ U.ι
    have hj : Set.range j = connectedComponentIn (g ⁻¹' {t}) (σ t) := by
      ext p
      constructor
      · rintro ⟨y, rfl⟩
        have ht : h (h.fiberι t y) = t := by
          rw [← Scheme.Hom.comp_apply, Scheme.Hom.fiber_fac,
            Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
        have hy := (h.fiberι t y).2
        change U.ι (h.fiberι t y) ∈
          connectedComponentIn (g ⁻¹' {g (U.ι (h.fiberι t y))})
            (σ (g (U.ι (h.fiberι t y)))) at hy
        change g (U.ι (h.fiberι t y)) = t at ht
        simpa only [ht, j, Scheme.Hom.comp_apply] using hy
      · intro hp
        have hpt : g p = t := connectedComponentIn_subset (g ⁻¹' {t}) (σ t) hp
        have hpU : p ∈ U := by
          change p ∈ connectedComponentIn (g ⁻¹' {g p}) (σ (g p))
          rwa [hpt]
        have hz : (⟨p, hpU⟩ : U.toScheme) ∈ Set.range (h.fiberι t) := by
          rw [h.range_fiberι]
          exact hpt
        obtain ⟨y, hy⟩ := hz
        exact ⟨y, by simp [j, hy]⟩
    have : ConnectedSpace (connectedComponentIn (g ⁻¹' {t}) (σ t)) :=
      Subtype.connectedSpace (isConnected_connectedComponentIn_iff.mpr
        (show σ t ∈ g ⁻¹' {t} from hsec t))
    exact (j.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hj)).connectedSpace_iff.mpr
      inferInstance
  have hgeo : GeometricallyConnected h := by
    rw [GeometricallyConnected.iff_geometricallyConnected_fiber]
    intro t
    have := hconnected t
    let s : Spec (T.residueField t) ⟶ h.fiber t :=
      pullback.lift (T.fromSpecResidueField t ≫ τ) (𝟙 _)
        (by simp [Category.assoc, hτ])
    exact GeometricallyConnected.of_connectedSpace_of_section
      (h.fiberToSpecResidueField t) s (pullback.lift_snd _ _ _)
  have hirr : GeometricallyIrreducible h := by
    refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ y ↦ ?_⟩
    have : GeometricallyConnected h := hgeo
    have : ConnectedSpace (pullback h y : Scheme.{u}) := inferInstance
    have : IsLocallyNoetherian (pullback h y : Scheme.{u}) :=
      LocallyOfFiniteType.isLocallyNoetherian (pullback.snd h y)
    exact irreducibleSpace_of_isDomain_stalk _ fun z ↦ by
      have := Smooth.isRegularLocalRing_stalk (pullback.snd h y) z
      infer_instance
  exact ⟨U, hσU, hirr, fun p hp ↦ hp⟩

/-- The slicing of a smooth morphism `f` near a point, for `f` quasi-compact and
quasi-separated; see `AlgebraicGeometry.Smooth.exists_etale_factorization_of_mem`. -/
private theorem exists_etale_factorization_of_mem_aux {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f]
    [QuasiCompact f] [QuasiSeparated f]
    (x : X) :
    ∃ (U : Scheme.{u}) (p : U ⟶ X) (V : Scheme.{u}) (q : U ⟶ V) (r : V ⟶ S),
      Etale p ∧ x ∈ Set.range p ∧ Etale r ∧ Smooth q ∧ IsAffine U ∧ IsAffine V ∧
      GeometricallyConnected q ∧ (∃ s : V ⟶ U, s ≫ q = 𝟙 V) ∧ q ≫ r = p ≫ f := by
  -- a point `x'` with finite separable residue field in the connected component of `x`
  obtain ⟨W, hxW, hW⟩ := f.exists_opens_inter_preimage_subset_connectedComponentIn x
  obtain ⟨x', hx'W, hfx', hx'⟩ := Smooth.exists_mem_etale_residueFieldMap f W hxW
  have hxx' : x ∈ connectedComponentIn (f ⁻¹' {f x}) x' := by
    rw [← connectedComponentIn_eq (hW ⟨hx'W, hfx'⟩)]
    exact mem_connectedComponentIn rfl
  -- an étale slice `ι: Z ⟶ X` through `x'`, and the section `σ` of `X ×_S Z ⟶ Z`
  obtain ⟨Z, ι, z, hZ, hιf, rfl⟩ := Smooth.exists_etale_comp_of_etale_residueFieldMap f hx'
  let σ : Z ⟶ pullback f (ι ≫ f) := pullback.lift ι (𝟙 Z) (by rw [Category.id_comp])
  have hσ : σ ≫ pullback.snd f (ι ≫ f) = 𝟙 Z := pullback.lift_snd _ _ _
  rw [← hfx'] at hxx'
  have hσz : pullback.snd f (ι ≫ f) (σ z) = z := by
    rw [← Scheme.Hom.comp_apply, hσ]
    rfl
  have hσx : pullback.fst f (ι ≫ f) (σ z) = ι z := by
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
  obtain ⟨p₀, hp₀, hp₀x⟩ := connectedComponentIn_subset_image_pullback_fst f (ι ≫ f) (σ z) hσz
    (by rwa [hσx, Scheme.Hom.comp_apply])
  have hp₀z : pullback.snd f (ι ≫ f) p₀ = z := 
    connectedComponentIn_subset (pullback.snd f (ι ≫ f) ⁻¹' {z}) _ hp₀
  -- the relative connected component `P₀` of `σ`
  obtain ⟨P₀, -, hP₀, hP₀'⟩ :=
    Smooth.exists_geometricallyIrreducible_of_section (pullback.snd f (ι ≫ f)) σ hσ
  have hp₀P₀ : p₀ ∈ P₀ := hP₀' p₀ (by rwa [hp₀z])
  -- an affine open `A` of `P₀` around `p₀`, and its open image `T` in `Z`
  set h := P₀.ι ≫ pullback.snd f (ι ≫ f)
  obtain ⟨A, hA, hp₀A, -⟩ := exists_isAffineOpen_mem_and_subset (X := P₀.toScheme) (U := ⊤)
    (x := (⟨p₀, hp₀P₀⟩ : P₀.toScheme)) trivial
  let T : Z.Opens := ⟨h '' A, h.isOpenMap _ A.2⟩
  have hAT : A ≤ h ⁻¹ᵁ T := fun a ha ↦ ⟨a, ha, rfl⟩
  let k := h.resLE T A hAT
  have : IsAffine A := hA
  have : Surjective k := ⟨by
    rintro ⟨_, a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, Subtype.ext (by simp [k, -Scheme.Hom.comp_base])⟩⟩
  have : GeometricallyIrreducible k := by
    have : Surjective (P₀.toScheme.homOfLE hAT ≫ h ∣_ T) := ‹Surjective k›
    exact inferInstanceAs (GeometricallyIrreducible (P₀.toScheme.homOfLE hAT ≫ h ∣_ T))
  -- a second étale slice `ι': Z' ⟶ A`, through a point of the fibre of `A ⟶ T` containing `p₀`
  obtain ⟨a', -, hka', ha'⟩ :=
    Smooth.exists_mem_etale_residueFieldMap k ⊤ (x := ⟨⟨p₀, hp₀P₀⟩, hp₀A⟩) trivial
  obtain ⟨Z', ι', z', hZ', hι'k, rfl⟩ := Smooth.exists_etale_comp_of_etale_residueFieldMap k ha'
  have : IsAffineHom (k ≫ T.ι) := by
    rw [Scheme.Hom.resLE_comp_ι]
    infer_instance
  have : IsAffineHom k := IsAffineHom.of_comp k T.ι
  refine ⟨pullback k (ι' ≫ k), pullback.fst _ _ ≫ A.ι ≫ P₀.ι ≫ pullback.fst f (ι ≫ f), Z',
    pullback.snd _ _, ι' ≫ k ≫ T.ι ≫ ι ≫ f, inferInstance, ?_, ?_, inferInstance,
    inferInstance, hZ', inferInstance,
    ⟨pullback.lift ι' (𝟙 Z') (Category.id_comp _).symm, pullback.lift_snd _ _ _⟩, ?_⟩
  · obtain ⟨u, hu, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := k) (g := ι' ≫ k)
      ⟨⟨p₀, hp₀P₀⟩, hp₀A⟩ z' (by simpa using hka'.symm)
    exact ⟨u, by simp [hu, hp₀x]⟩
  · have : Etale (ι' ≫ k ≫ T.ι) := by
      rw [← Category.assoc]
      infer_instance
    rw [← Category.assoc, ← Category.assoc]
    infer_instance
  · have H := pullback.condition (f := f) (g := ι ≫ f)
    rw [← Category.assoc ι' k, ← pullback.condition_assoc]
    simp only [k, h, Scheme.Hom.resLE_comp_ι_assoc, Category.assoc] at H ⊢
    rw [← H]

/-- **Slicing a smooth morphism at a point.** Let `f : X ⟶ S` be smooth and `x : X`. Then there
are an étale `p : U ⟶ X` with `x` in its image and a factorisation `p ≫ f = q ≫ r` with
`r : V ⟶ S` étale and `q : U ⟶ V` a smooth morphism of affine schemes with geometrically connected
fibres and a section. -/
theorem Smooth.exists_etale_factorization_of_mem {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f]
    (x : X) :
    ∃ (U : Scheme.{u}) (p : U ⟶ X) (V : Scheme.{u}) (q : U ⟶ V) (r : V ⟶ S),
      Etale p ∧ x ∈ Set.range p ∧ Etale r ∧ Smooth q ∧ IsAffine U ∧ IsAffine V ∧
      GeometricallyConnected q ∧ (∃ s : V ⟶ U, s ≫ q = 𝟙 V) ∧ q ≫ r = p ≫ f := by
  obtain ⟨S', hS', hxS', -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := f x) trivial
  obtain ⟨X', hX', hxX', hX'S'⟩ :=
    exists_isAffineOpen_mem_and_subset (U := f ⁻¹ᵁ S') (x := x) hxS'
  have : IsAffine S' := hS'
  have : IsAffine X' := hX'
  obtain ⟨U, p, V, q, r, hp, ⟨u, hu⟩, hr, hq, hU, hV, hqc, hs, hqr⟩ :=
    exists_etale_factorization_of_mem_aux (f.resLE S' X' hX'S') ⟨x, hxX'⟩
  refine ⟨U, p ≫ X'.ι, V, q, r ≫ S'.ι, inferInstance, ⟨u, by simp [hu]⟩, inferInstance, hq, hU,
    hV, hqc, hs, ?_⟩
  rw [← Category.assoc, hqr, Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc]

/-- **Slicing a smooth morphism**. Let
`f: X ⟶ S` be smooth. Then there is an étale covering `p i: U i ⟶ X` of `X` such that each
composite `p i ≫ f` factors as `q i ≫ r i` with `r i: V i ⟶ S` étale and `q i: U i ⟶ V i` a smooth
morphism of affine schemes with geometrically connected fibres admitting a section:

```
U i --q i--> V i
 |            |
p i          r i
 v            v
 X ----f----> S
```
-/
@[stacks 0EY4]
theorem Smooth.exists_etaleCover_factorization {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] :
    ∃ (ι : Type u) (U : ι → Scheme.{u}) (p : ∀ i, U i ⟶ X) (V : ι → Scheme.{u})
      (q : ∀ i, U i ⟶ V i) (r : ∀ i, V i ⟶ S),
      (∀ i, Etale (p i)) ∧ (∀ x : X, ∃ (i : ι) (y : U i), (p i).base y = x) ∧
      (∀ i, Etale (r i)) ∧ (∀ i, Smooth (q i)) ∧ (∀ i, IsAffine (U i)) ∧
      (∀ i, IsAffine (V i)) ∧ (∀ i, GeometricallyConnected (q i)) ∧
      (∀ i, ∃ s : V i ⟶ U i, s ≫ q i = 𝟙 (V i)) ∧ (∀ i, q i ≫ r i = p i ≫ f) := by
  choose U p V q r hp hx hr hq hU hV hqc hs hqr using Smooth.exists_etale_factorization_of_mem f
  exact ⟨X, U, p, V, q, r, hp, fun x ↦ ⟨x, hx x⟩, hr, hq, hU, hV, hqc, hs, hqr⟩

end AlgebraicGeometry
