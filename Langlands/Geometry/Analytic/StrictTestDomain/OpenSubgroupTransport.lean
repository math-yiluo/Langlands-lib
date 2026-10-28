import Langlands.Geometry.Analytic.StrictTestDomain.InvariantConjugationSite
import Langlands.Geometry.Analytic.StrictTestDomain.InvariantSubgroupRestriction
import Langlands.Geometry.Analytic.StrictTestDomain.RationalTransport

/-! # Rational transport with actual open operator subgroups -/

noncomputable section

universe u v

namespace Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction

open CategoryTheory

attribute [local instance] NormContinuousAffinoidAction.topCatSelfForget

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (ρ : RationalSpectralAction G P)

/-- A chosen actual rational quotient with an actual open subgroup preserving
its locus. The quotient presentation and the subgroup are both retained. -/
structure OpenSubgroupTransport where
  subgroup : OpenSubgroup G
  domain : ρ.InvariantRationalDomain subgroup

namespace OpenSubgroupTransport

variable {ρ}

/-- A group label gives a conjugation-compatible map of the actual rational
loci. Distinct labels remain distinct even when their operators agree. -/
structure Hom (X Y : ρ.OpenSubgroupTransport) where
  label : G
  subgroup_le : conjugateOpenSubgroup X.subgroup label ≤ Y.subgroup
  mapsTo : ∀ x ∈ X.domain.obj.locus, ρ.toMonoidHom label • x ∈ Y.domain.obj.locus

@[ext]
theorem Hom.ext {X Y : ρ.OpenSubgroupTransport} {f g : Hom X Y}
    (h : f.label = g.label) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- Composition uses the actual product of labels, in point-action order. -/
instance : Category (ρ.OpenSubgroupTransport) where
  Hom := Hom
  id X :=
    ⟨1, by intro k hk; simpa using hk,
      by intro x hx; simpa using hx⟩
  comp f g :=
    ⟨g.label * f.label, by
      intro k hk
      apply g.subgroup_le
      rw [mem_conjugateOpenSubgroup] at hk ⊢
      apply f.subgroup_le
      rw [mem_conjugateOpenSubgroup]
      simpa only [mul_inv_rev, mul_assoc] using hk,
      by
        intro x hx
        simpa only [map_mul, mul_smul] using g.mapsTo _ (f.mapsTo _ hx)⟩
  id_comp f := Hom.ext (mul_one _)
  comp_id f := Hom.ext (one_mul _)
  assoc f g h := Hom.ext (mul_assoc _ _ _).symm

@[simp]
theorem id_label (X : ρ.OpenSubgroupTransport) :
    (𝟙 X : X ⟶ X).label = 1 := rfl

@[simp]
theorem comp_label {X Y Z : ρ.OpenSubgroupTransport} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).label = g.label * f.label := rfl

/-- Forget the subgroup but retain the actual automorphism-labelled locus map.
This need not be faithful when the given group action has a kernel. -/
def toRationalTransport : ρ.OpenSubgroupTransport ⥤ RationalTransport K P where
  obj X := ⟨X.domain.obj⟩
  map f := ⟨ρ.toMonoidHom f.label, f.mapsTo⟩
  map_id _ := RationalTransport.Hom.ext (map_one _)
  map_comp _ _ := RationalTransport.Hom.ext (map_mul _ _ _)

/-- The constructed continuous action of the object's actual open subgroup on
the actual quotient spectrum. -/
def spectrum (X : ρ.OpenSubgroupTransport) : ContAction TopCat.{u} X.subgroup :=
  ρ.invariantSpectrum X.subgroup X.domain

/-- The fixed-subgroup rational inclusion diagram sits inside the category with
varying open subgroups via identity-labelled arrows. -/
def inclusion (U : OpenSubgroup G) :
    ρ.InvariantRationalDomain U ⥤ ρ.OpenSubgroupTransport where
  obj d := ⟨U, d⟩
  map h := ⟨1, by intro k hk; simpa using hk,
    by intro x hx; simpa using h.hom.subset hx⟩
  map_id _ := Hom.ext rfl
  map_comp _ _ := Hom.ext (one_mul _).symm

/-- Subgroup restriction gives an arrow in the direction of the actual
continuous subgroup inclusion, with the quotient presentation unchanged. -/
def subgroupRestriction {U V : OpenSubgroup G} (h : V ≤ U)
    (d : ρ.InvariantRationalDomain U) :
    (inclusion V).obj ((ρ.invariantRestrictionFunctor h).obj d) ⟶
      (inclusion U).obj d := by
  refine ⟨1, ?_, ?_⟩
  · change conjugateOpenSubgroup V 1 ≤ U
    intro k hk
    exact h (by simpa using hk)
  · intro x hx
    change x ∈ d.obj.locus at hx
    change ρ.toMonoidHom 1 • x ∈ d.obj.locus
    simpa using hx

/-- These subgroup-change arrows commute with every actual rational inclusion. -/
def subgroupRestrictionNatTrans {U V : OpenSubgroup G} (h : V ≤ U) :
    ρ.invariantRestrictionFunctor h ⋙ inclusion V ⟶ inclusion U where
  app d := subgroupRestriction h d
  naturality _ _ _ := Hom.ext (by simp [subgroupRestriction, inclusion])

/-- Actual conjugation and rational presentation transport define an
isomorphism in the category with varying open subgroups. -/
def translationIso (U : OpenSubgroup G) (g : G) (d : ρ.InvariantRationalDomain U) :
    (inclusion U).obj d ≅
      (inclusion (conjugateOpenSubgroup U g)).obj
        ((ρ.invariantConjugationEquivalence U g).functor.obj d) where
  hom := ⟨g, le_refl _, fun x hx =>
    (smul_mem_smul_locus_iff (ρ.toMonoidHom g) d.obj x).mpr hx⟩
  inv := ⟨g⁻¹, by
    change conjugateOpenSubgroup (conjugateOpenSubgroup U g) g⁻¹ ≤ U
    rw [conjugateOpenSubgroup_inv], by
    intro x hx
    change x ∈ (ρ.toMonoidHom g • d.obj).locus at hx
    apply (smul_mem_smul_locus_iff (ρ.toMonoidHom g) d.obj
      (ρ.toMonoidHom g⁻¹ • x)).mp
    simpa only [map_inv, smul_inv_smul] using hx⟩
  hom_inv_id := Hom.ext (inv_mul_cancel g)
  inv_hom_id := Hom.ext (mul_inv_cancel g)

namespace Hom

variable {X Y Z : ρ.OpenSubgroupTransport}

/-- The actual continuous homomorphism of operator subgroups carried by a map. -/
def groupHom (f : X ⟶ Y) : X.subgroup →ₜ* Y.subgroup where
  toFun k :=
    ⟨f.label * (k : G) * f.label⁻¹, f.subgroup_le (by
      rw [mem_conjugateOpenSubgroup]
      simp [mul_assoc, k.property])⟩
  map_one' := Subtype.ext (by simp)
  map_mul' k l := Subtype.ext (by simp [mul_assoc])
  continuous_toFun :=
    ((IsTopologicalGroup.continuous_conj f.label).comp
      continuous_subtype_val).subtype_mk _

@[simp]
theorem groupHom_apply (f : X ⟶ Y) (k : X.subgroup) :
    (f.groupHom k : G) = f.label * (k : G) * f.label⁻¹ := rfl

@[simp]
theorem groupHom_id (X : ρ.OpenSubgroupTransport) :
    (𝟙 X : X ⟶ X).groupHom = ContinuousMonoidHom.id X.subgroup := by
  ext k
  simp

@[simp]
theorem groupHom_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).groupHom = g.groupHom.comp f.groupHom := by
  ext k
  simp [mul_assoc]

/-- The rational universal property supplies the bounded pullback on the actual
quotient algebras; this is the published labelled restriction. -/
def restriction (f : X ⟶ Y) :
    BoundedAlgHom K Y.domain.obj.algebra X.domain.obj.algebra :=
  (toRationalTransport.map f).restriction

@[simp]
theorem restriction_comp_baseMap (f : X ⟶ Y) :
    f.restriction.comp Y.domain.obj.baseMap =
      X.domain.obj.baseMap.comp (ρ.toMonoidHom f.label).inv :=
  (toRationalTransport.map f).restriction_comp_baseMap

@[simp]
theorem restriction_id (X : ρ.OpenSubgroupTransport) :
    (𝟙 X : X ⟶ X).restriction = BoundedAlgHom.id K X.domain.obj.algebra := by
  change (toRationalTransport.map (𝟙 X)).restriction =
    BoundedAlgHom.id K (toRationalTransport.obj X).data.algebra
  rw [CategoryTheory.Functor.map_id, RationalTransport.Hom.restriction_id]

@[simp]
theorem restriction_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).restriction = f.restriction.comp g.restriction := by
  change (toRationalTransport.map (f ≫ g)).restriction = _
  rw [CategoryTheory.Functor.map_comp, RationalTransport.Hom.restriction_comp]
  rfl

/-- The actual continuous quotient-spectrum map lies over the labelled point
action on the ambient spectrum. -/
theorem spectrumMap_restriction (f : X ⟶ Y)
    (x : BanachSpectrum X.domain.obj.algebra) :
    Y.domain.obj.spectrumMap (BanachSpectrum.comap f.restriction.toBoundedRingHom x) =
      ρ.toMonoidHom f.label • X.domain.obj.spectrumMap x :=
  (toRationalTransport.map f).spectrumMap_restriction x

/-- Pullback intertwines the forward section action with the actual conjugation
homomorphism of open subgroups. -/
theorem sectionAction_restriction (f : X ⟶ Y) (k : X.subgroup) :
    f.restriction.comp
        (ρ.sectionAction Y.domain.obj
          (ρ.invariantStabilizerInclusion Y.subgroup Y.domain (f.groupHom k))).hom =
      (ρ.sectionAction X.domain.obj
        (ρ.invariantStabilizerInclusion X.subgroup X.domain k)).hom.comp
          f.restriction := by
  apply Y.domain.obj.hom_ext
  conv_lhs =>
    rw [BoundedAlgHom.comp_assoc, ρ.sectionAction_comp_baseMap,
      ← BoundedAlgHom.comp_assoc, f.restriction_comp_baseMap]
  conv_rhs =>
    rw [BoundedAlgHom.comp_assoc, f.restriction_comp_baseMap,
      ← BoundedAlgHom.comp_assoc, ρ.sectionAction_comp_baseMap]
  have hlabel : (ρ.toMonoidHom f.label)⁻¹ *
        ρ.toMonoidHom (f.groupHom k : G) =
      ρ.toMonoidHom (k : G) * (ρ.toMonoidHom f.label)⁻¹ := by
    simp [map_mul, map_inv, mul_assoc]
  exact congrArg (fun a : Aut P => X.domain.obj.baseMap.comp a.hom) hlabel

/-- The actual continuous spectrum map is equivariant for conjugation of
operator subgroups. -/
theorem spectrum_equivariant (f : X ⟶ Y) (k : X.subgroup)
    (x : BanachSpectrum X.domain.obj.algebra) :
    BanachSpectrum.comap f.restriction.toBoundedRingHom
        ((ρ.sectionAction X.domain.obj
          (ρ.invariantStabilizerInclusion X.subgroup X.domain k)) • x) =
      (ρ.sectionAction Y.domain.obj
        (ρ.invariantStabilizerInclusion Y.subgroup Y.domain (f.groupHom k))) •
          BanachSpectrum.comap f.restriction.toBoundedRingHom x := by
  apply BanachSpectrum.ext
  intro a
  have ht := f.sectionAction_restriction k⁻¹
  rw [map_inv, map_inv, map_inv, map_inv, map_inv] at ht
  exact congrArg (fun q : BoundedAlgHom K Y.domain.obj.algebra X.domain.obj.algebra =>
    x (q a)) ht.symm

/-- The bounded pullback yields a morphism of actual continuous actions, after
restricting the target action along the continuous conjugation homomorphism. -/
def equivariantSpectrumMap (f : X ⟶ Y) :
    X.spectrum ⟶ (ContAction.res TopCat.{u} f.groupHom).obj Y.spectrum :=
  ObjectProperty.homMk
    { hom := TopCat.ofHom (BanachSpectrum.comapContinuous f.restriction.toBoundedRingHom)
      comm := fun k => by
        apply TopCat.ext
        intro x
        exact f.spectrum_equivariant k x }

@[simp]
theorem equivariantSpectrumMap_apply (f : X ⟶ Y)
    (x : BanachSpectrum X.domain.obj.algebra) :
    f.equivariantSpectrumMap.hom.hom x =
      BanachSpectrum.comap f.restriction.toBoundedRingHom x := rfl

end Hom

@[simp]
theorem inclusion_restriction (U : OpenSubgroup G)
    {d e : ρ.InvariantRationalDomain U} (h : d ⟶ e) :
    ((inclusion U).map h).restriction = h.hom.restriction := by
  change (toRationalTransport.map ((inclusion U).map h)).restriction = _
  have hp : toRationalTransport.map ((inclusion U).map h) =
      RationalTransport.inclusion.map h.hom :=
    RationalTransport.Hom.ext (map_one _)
  rw [hp]
  exact RationalTransport.inclusion_restriction h.hom

@[simp]
theorem subgroupRestriction_groupHom {U V : OpenSubgroup G} (h : V ≤ U)
    (d : ρ.InvariantRationalDomain U) :
    (subgroupRestriction h d).groupHom = openSubgroupInclusion h := by
  ext k
  change (1 : G) * (k : G) * 1⁻¹ = (k : G)
  simp

/-- Changing only the subgroup acts by the actual identity on quotient sections. -/
@[simp]
theorem subgroupRestriction_restriction {U V : OpenSubgroup G} (h : V ≤ U)
    (d : ρ.InvariantRationalDomain U) :
    (subgroupRestriction h d).restriction = BoundedAlgHom.id K d.obj.algebra := by
  apply d.obj.hom_ext
  calc
    _ = d.obj.baseMap.comp (ρ.toMonoidHom 1).inv :=
      (subgroupRestriction h d).restriction_comp_baseMap
    _ = _ := by rw [map_one]; rfl

/-- Realize every object and arrow by the constructed strict affinoid quotient
and its bounded map, contravariantly. -/
def toAffinoidSpace : ρ.OpenSubgroupTransport ⥤ PresentedStrictAffinoidSpace K :=
  toRationalTransport ⋙ RationalTransport.toAffinoidSpace

/-- The quotient spectra and their actual continuous maps. -/
def toTopologicalSpace : ρ.OpenSubgroupTransport ⥤ TopCat :=
  toRationalTransport ⋙ RationalTransport.toTopologicalSpace

/-- The actual bounded quotient-algebra presheaf on subgroup-labelled maps. -/
def boundedPresheaf :
    (ρ.OpenSubgroupTransport)ᵒᵖ ⥤ PresentedStrictAffinoidAlgebra K :=
  toRationalTransport.op ⋙ RationalTransport.boundedPresheaf

/-- Forget norms to obtain the actual commutative algebra presheaf. -/
def algebraPresheaf : (ρ.OpenSubgroupTransport)ᵒᵖ ⥤ CommAlgCat K :=
  boundedPresheaf ⋙ PresentedStrictAffinoidAlgebra.toCommAlgCat K

end OpenSubgroupTransport

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction
