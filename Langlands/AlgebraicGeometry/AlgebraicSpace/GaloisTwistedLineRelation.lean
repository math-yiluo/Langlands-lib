import Langlands.AlgebraicGeometry.AlgebraicSpace.GaloisTwistedLineRing
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# The étale equivalence relation of the Galois-twisted line

`U = Spec K'[X]` and `R = Spec (K'[X] × K'[X, 1/X])`, with `t` and `s` the spectra of the two
relation maps. On `T`-valued points, `R` consists of the pairs of points of the line that lie over
the same point of the `K`-line and are either equal, or conjugate where the coordinate is a unit.
This is an étale equivalence relation in the sense of the Library
(`Langlands.AlgebraicGeometry.EtaleEquivalenceRelation`).
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Polynomial
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace GaloisTwistedLine

/-! ### Points of affine schemes as ring maps -/

section Points

variable {T : Scheme.{u}} {R S : Type u} [CommRing R] [CommRing S]

/-- The morphism to an affine scheme given by a ring map to global sections. -/
def toSpec (φ : R →+* Γ(T, ⊤)) : T ⟶ Spec (CommRingCat.of R) :=
  T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ)

/-- The ring map to global sections of a morphism to an affine scheme. -/
def ofSpec (g : T ⟶ Spec (CommRingCat.of R)) : R →+* Γ(T, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g.appTop).hom

theorem toSpec_ofSpec (g : T ⟶ Spec (CommRingCat.of R)) : toSpec (ofSpec g) = g := by
  unfold toSpec ofSpec
  rw [CommRingCat.ofHom_hom, Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality,
    Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

theorem ofSpec_comp (g : T ⟶ Spec (CommRingCat.of R)) (f : S →+* R) :
    ofSpec (g ≫ Spec.map (CommRingCat.ofHom f)) = (ofSpec g).comp f := by
  unfold ofSpec
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality,
    Category.assoc]
  rfl

theorem ofSpec_injective : Function.Injective (ofSpec : (T ⟶ Spec (CommRingCat.of R)) → _) :=
  fun g h e => by rw [← toSpec_ofSpec g, ← toSpec_ofSpec h, e]

theorem ofSpec_toSpec (φ : R →+* Γ(T, ⊤)) : ofSpec (toSpec φ) = φ := by
  have h : ofSpec (T.toSpecΓ : T ⟶ Spec (CommRingCat.of Γ(T, ⊤))) = RingHom.id _ := by
    unfold ofSpec
    rw [Scheme.toSpecΓ_appTop, Iso.inv_hom_id]
    rfl
  unfold toSpec
  rw [ofSpec_comp, h]
  rfl

end Points

/-! ### The relation -/

variable {K K' : Type u} [Field K] [Field K'] [Algebra K K'] (D : QuadraticConj K K')

variable (K') in
/-- The line `Spec K'[X]`. -/
abbrev lineScheme : Scheme.{u} := Spec (CommRingCat.of K'[X])

variable (K') in
/-- The relation scheme `Spec (K'[X] × K'[X, 1/X])`. -/
abbrev relationScheme : Scheme.{u} := Spec (CommRingCat.of (RelationRing K'))

variable (K') in
/-- The first projection of the relation. -/
def tMap : relationScheme K' ⟶ lineScheme K' := Spec.map (CommRingCat.ofHom tStar)

/-- The second projection of the relation. -/
def sMap : relationScheme K' ⟶ lineScheme K' := Spec.map (CommRingCat.ofHom (sStar D))

theorem ofSpec_comp_tMap {T : Scheme.{u}} (g : T ⟶ relationScheme K') :
    ofSpec (g ≫ tMap K') = (ofSpec g).comp tStar := ofSpec_comp g _

theorem ofSpec_comp_sMap {T : Scheme.{u}} (g : T ⟶ relationScheme K') :
    ofSpec (g ≫ sMap D) = (ofSpec g).comp (sStar D) := ofSpec_comp g _

theorem etale_tMap : Etale (tMap K') := by
  have : IsZariskiLocalAtSource @Etale.{u} := HasRingHomProperty.instIsZariskiLocalAtSource
  have key : Etale (coprodSpec K'[X] (PuncturedRing K') ≫ tMap K') := by
    apply IsZariskiLocalAtSource.of_openCover (P := @Etale) (coprodOpenCover.{u, 0} _ _)
    rintro (⟨⟩ | ⟨⟩)
    · change Etale (coprod.inl ≫ coprodSpec _ _ ≫ tMap K')
      rw [coprodSpec_inl_assoc, tMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      have : (RingHom.fst K'[X] (PuncturedRing K')).comp tStar = RingHom.id _ := rfl
      rw [this, CommRingCat.ofHom_id, Spec.map_id]
      infer_instance
    · change Etale (coprod.inr ≫ coprodSpec _ _ ≫ tMap K')
      rw [coprodSpec_inr_assoc, tMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      have : (RingHom.snd K'[X] (PuncturedRing K')).comp tStar =
          algebraMap K'[X] (PuncturedRing K') := rfl
      rw [this, HasRingHomProperty.Spec_iff (P := @Etale), CommRingCat.hom_ofHom,
        RingHom.etale_algebraMap]
      infer_instance
  have : tMap K' = inv (coprodSpec K'[X] (PuncturedRing K')) ≫
      (coprodSpec K'[X] (PuncturedRing K') ≫ tMap K') := by simp
  rw [this]
  infer_instance

theorem etale_sMap : Etale (sMap D) := by
  have hs : sMap D = Spec.map (CommRingCat.ofHom (swapStar D)) ≫ tMap K' := by
    rw [tMap, sMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, swapStar_comp_tStar]
  have hid : Spec.map (CommRingCat.ofHom (swapStar D)) ≫
      Spec.map (CommRingCat.ofHom (swapStar D)) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, swapStar_swapStar, CommRingCat.ofHom_id,
      Spec.map_id]
  have : IsIso (Spec.map (CommRingCat.ofHom (swapStar D))) := ⟨⟨_, hid, hid⟩⟩
  rw [hs]
  have := etale_tMap (K' := K')
  infer_instance

/-- **The étale equivalence relation of the Galois-twisted line.** -/
abbrev relation : EtaleEquivalenceRelation.{u} where
  U := lineScheme K'
  R := relationScheme K'
  t := tMap K'
  s := sMap D
  mono_lift := ⟨fun {T} g h hgh => by
    have h1 : g ≫ tMap K' = h ≫ tMap K' := by simpa using congrArg (· ≫ prod.fst) hgh
    have h2 : g ≫ sMap D = h ≫ sMap D := by simpa using congrArg (· ≫ prod.snd) hgh
    apply ofSpec_injective
    apply hom_ext D
    · rw [← ofSpec_comp_tMap, ← ofSpec_comp_tMap, h1]
    · rw [← ofSpec_comp_sMap, ← ofSpec_comp_sMap, h2]⟩
  refl T a := by
    refine ⟨toSpec ((ofSpec a).comp (RingHom.fst _ _)), ?_, ?_⟩
    · apply ofSpec_injective
      rw [ofSpec_comp_tMap, ofSpec_toSpec]
      rfl
    · apply ofSpec_injective
      rw [ofSpec_comp_sMap, ofSpec_toSpec]
      rfl
  symm T r := by
    refine ⟨r ≫ Spec.map (CommRingCat.ofHom (swapStar D)), ?_, ?_⟩
    · rw [Category.assoc, tMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, swapStar_comp_tStar]
      rfl
    · rw [Category.assoc, sMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, swapStar_comp_sStar]
      rfl
  trans T r r' e := by
    have he : (ofSpec r).comp (sStar D) = (ofSpec r').comp tStar := by
      rw [← ofSpec_comp_sMap, ← ofSpec_comp_tMap, e]
    have hxy := sameBase_of_hom D (ofSpec r)
    have hyz := sameBase_of_hom D (ofSpec r')
    rw [← he] at hyz
    have hu1 := isUnit_pairUnit_of_hom D (ofSpec r)
    have hu2 := isUnit_pairUnit_of_hom D (ofSpec r')
    rw [← he] at hu2
    have hxz : SameBase K ((ofSpec r).comp tStar) ((ofSpec r').comp (sStar D)) :=
      ⟨fun k => (hxy.1 k).trans (hyz.1 k), hxy.2.trans hyz.2⟩
    have hu := isUnit_pairUnit_trans D hxy hyz hu1 hu2
    refine ⟨toSpec (relHom D hxz hu), ?_, ?_⟩
    · apply ofSpec_injective
      rw [ofSpec_comp_tMap, ofSpec_toSpec, relHom_comp_tStar, ofSpec_comp_tMap]
    · apply ofSpec_injective
      rw [ofSpec_comp_sMap, ofSpec_toSpec, relHom_comp_sStar, ofSpec_comp_sMap]
  etale_t := etale_tMap
  etale_s := etale_sMap D

/-- The structure map of the line to `Spec K`. -/
abbrev lineBase : lineScheme K' ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K K'[X]))

theorem tMap_lineBase : tMap K' ≫ lineBase (K := K) = sMap D ≫ lineBase := by
  rw [tMap, sMap, lineBase, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp]
  congr 2
  refine RingHom.ext fun k => Prod.ext rfl ?_
  simp [tStar, sStar, AlgEquiv.commutes]

end GaloisTwistedLine

end Langlands.AlgebraicGeometry.AlgebraicSpace
