import Langlands.Representation.Induction.QuotientAdjunction
import Langlands.Cohomology.DivisibleSystem.Sections
import Langlands.Representation.Category.Abelian
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RepresentationTheory.Rep.Res

/-!
# Invariants of `ℓ`-divisible systems of complexes

Harris 1999, §2, p.305, takes an open normal pro-`p` subgroup `H` of `S(ẽ)` acting trivially
on the cohomology, notes that `H⁰(H, ·)` is exact on `ℓ`-primary torsion modules, and obtains
from the inclusion `G_m^•(U(ẽ)_F̄)^H ↪ G_m^•(U(ẽ)_F̄)` "an `ℓ`-divisible system of
finite-length complexes of `ℤ/ℓ^mℤ[S(ẽ)/H]`-modules, in the obvious sense".

For a normal subgroup `H` of `G`, Mathlib's functor `Rep.quotientToInvariantsFunctor`
sends a representation of `G` to the representation of `G ⧸ H` on its `H`-invariants. This
module shows that it is additive and preserves limits, and that the inclusion of smooth
representations preserves finite limits. It applies the composite degreewise to an
`ℓ`-divisible system of complexes of smooth representations, given that every degree of every
projection `j` stays an epimorphism on `H`-invariants. It also constructs the inclusion of
the inflated invariants as a morphism of `ℓ`-divisible systems, and specializes everything to
the compact sections of the truncated smooth Godement resolutions. The surjectivity on
invariants is an explicit hypothesis. The exactness of pro-`p` invariants and the
quasi-isomorphism property of the inclusion are not proved here.
-/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u v' u' uR uG uV

section QuotientInvariants

variable (k : Type u) [CommRing k] {G : Type v} [Group G] (H : Subgroup G) [H.Normal]

/-- Taking `H`-invariants is additive. -/
instance quotientToInvariantsFunctor_additive :
    (Rep.quotientToInvariantsFunctor.{w} k H).Additive where
  map_add {X Y} f g := by
    ext x
    rfl

/-- Taking `H`-invariants preserves limits: followed by the forgetful functor to modules, which
reflects limits, it is the restriction to `H` followed by Mathlib's invariants functor, and both
preserve limits. -/
instance quotientToInvariantsFunctor_preservesLimits :
    PreservesLimitsOfSize.{w, w} (Rep.quotientToInvariantsFunctor.{w} k H) :=
  have : PreservesLimitsOfSize.{w, w} (Rep.quotientToInvariantsFunctor.{w} k H ⋙
      forget₂ (Rep.{w} k (G ⧸ H)) (ModuleCat.{w} k)) :=
    inferInstanceAs (PreservesLimitsOfSize.{w, w}
      (Rep.resFunctor.{w} H.subtype ⋙ Rep.invariantsFunctor.{w} k H))
  preservesLimits_of_reflects_of_preserves _ (forget₂ (Rep.{w} k (G ⧸ H)) (ModuleCat.{w} k))

end QuotientInvariants

section SmoothInvariants

variable (R : Type uR) [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G]

/-- The inclusion of smooth representations into all representations preserves finite
limits: smoothness is closed under kernels. -/
instance smoothRep_toRep_preservesFiniteLimits :
    PreservesFiniteLimits
      (SmoothRep.toRep : SmoothRep.{uR, uG, uV} R G ⥤ Rep.{uV} R G) :=
  have : ∀ {A B : SmoothRep.{uR, uG, uV} R G} (f : A ⟶ B),
      PreservesLimit (parallelPair f 0) SmoothRep.toRep :=
    fun f => (smoothRepProperty R G).preservesKernels_ι f
  Functor.preservesFiniteLimits_of_preservesKernels _

variable (H : Subgroup G) [H.Normal]

/-- The `H`-invariants of a smooth representation of `G`, as a representation of `G ⧸ H`. -/
abbrev smoothQuotientInvariants : SmoothRep.{uR, uG, uV} R G ⥤ Rep.{uV} R (G ⧸ H) :=
  SmoothRep.toRep ⋙ Rep.quotientToInvariantsFunctor R H

/-- The inclusion of the inflated `H`-invariants into the underlying representation. -/
abbrev smoothQuotientInvariantsInclusion :
    smoothQuotientInvariants.{uR, uG, uV} R H ⋙ Rep.resFunctor (QuotientGroup.mk' H) ⟶
      SmoothRep.toRep :=
  Functor.whiskerLeft SmoothRep.toRep (quotientInvariantsInclusion R H) ≫
    (Functor.rightUnitor _).hom

end SmoothInvariants

namespace DivisibleSystem

section NatTrans

variable {C : Type u} [Category.{v} C] [Abelian C] {E : Type u'} [Category.{v'} E] [Abelian E]
  {ℓ : ℕ}

/-- A natural transformation between additive functors preserving finite limits induces a
morphism of the image `ℓ`-divisible systems. -/
@[simps tower]
def mapLeftExactNatTrans (T : DivisibleSystem C ℓ) {F F' : C ⥤ E} [F.Additive]
    [PreservesFiniteLimits F] [F'.Additive] [PreservesFiniteLimits F'] (α : F ⟶ F')
    (hF : ∀ {m' m : ℕ} (h : m' ≤ m), Epi (F.map (T.projection h)))
    (hF' : ∀ {m' m : ℕ} (h : m' ≤ m), Epi (F'.map (T.projection h))) :
    T.mapLeftExact F hF ⟶ T.mapLeftExact F' hF' :=
  ⟨Functor.whiskerLeft T.tower α, fun h => α.naturality (T.inclusion h)⟩

/-- A natural transformation `Φ ⟶ Φ'` induces a morphism of the degreewise images of an
`ℓ`-divisible system of cochain complexes. -/
def mapComplexesNatTrans (K : DivisibleSystem (CochainComplex C ℕ) ℓ) {Φ Φ' : C ⥤ E}
    [Φ.Additive] [PreservesFiniteLimits Φ] [Φ'.Additive] [PreservesFiniteLimits Φ']
    (α : Φ ⟶ Φ')
    (hΦ : ∀ {m' m : ℕ} (h : m' ≤ m) (q : ℕ), Epi (Φ.map ((K.projection h).f q)))
    (hΦ' : ∀ {m' m : ℕ} (h : m' ≤ m) (q : ℕ), Epi (Φ'.map ((K.projection h).f q))) :
    K.mapComplexes Φ hΦ ⟶ K.mapComplexes Φ' hΦ' :=
  K.mapLeftExactNatTrans (NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ))
    (fun h => K.epi_mapHomologicalComplex_map_projection Φ hΦ h)
    (fun h => K.epi_mapHomologicalComplex_map_projection Φ' hΦ' h)

lemma mapComplexesNatTrans_tower_app_f (K : DivisibleSystem (CochainComplex C ℕ) ℓ)
    {Φ Φ' : C ⥤ E} [Φ.Additive] [PreservesFiniteLimits Φ] [Φ'.Additive]
    [PreservesFiniteLimits Φ'] (α : Φ ⟶ Φ')
    (hΦ : ∀ {m' m : ℕ} (h : m' ≤ m) (q : ℕ), Epi (Φ.map ((K.projection h).f q)))
    (hΦ' : ∀ {m' m : ℕ} (h : m' ≤ m) (q : ℕ), Epi (Φ'.map ((K.projection h).f q)))
    (m : ℕᵒᵖ) (q : ℕ) :
    ((K.mapComplexesNatTrans α hΦ hΦ').tower.app m).f q = α.app ((K.tower.obj m).X q) :=
  rfl

end NatTrans

section Smooth

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] {ℓ : ℕ}
  (K : DivisibleSystem (CochainComplex (SmoothRep.{uR, uG, uV} R G) ℕ) ℓ)

/-- Every degree of every projection of a system of complexes is an epimorphism. -/
lemma epi_projection_f {m' m : ℕ} (h : m' ≤ m) (q : ℕ) : Epi ((K.projection h).f q) :=
  (K.degree q).epi_projection h

lemma epi_toRep_map_projection_f {m' m : ℕ} (h : m' ≤ m) (q : ℕ) :
    Epi (SmoothRep.toRep.map ((K.projection h).f q)) :=
  have := K.epi_projection_f h q
  inferInstance

/-- The underlying `ℓ`-divisible system of complexes of algebraic representations. -/
def toRepComplexes : DivisibleSystem (CochainComplex (Rep.{uV} R G) ℕ) ℓ :=
  K.mapComplexes SmoothRep.toRep K.epi_toRep_map_projection_f

variable (H : Subgroup G) [H.Normal]

/-- The `H`-invariants of an `ℓ`-divisible system of complexes of smooth representations of
`G`, as an `ℓ`-divisible system of complexes of representations of `G ⧸ H`, given that every
degree of every projection stays an epimorphism on `H`-invariants. -/
def quotientInvariantsComplexes
    (hK : ∀ {m' m : ℕ} (h : m' ≤ m) (q : ℕ),
      Epi ((smoothQuotientInvariants R H).map ((K.projection h).f q))) :
    DivisibleSystem (CochainComplex (Rep.{uV} R (G ⧸ H)) ℕ) ℓ :=
  K.mapComplexes (smoothQuotientInvariants R H) hK

lemma quotientInvariantsComplexes_obj_X
    (hK : ∀ {m' m : ℕ} (h : m' ≤ m) (q : ℕ),
      Epi ((smoothQuotientInvariants R H).map ((K.projection h).f q)))
    (m q : ℕ) :
    ((K.quotientInvariantsComplexes H hK).obj m).X q =
      (Rep.quotientToInvariantsFunctor R H).obj (SmoothRep.toRep.obj ((K.obj m).X q)) :=
  rfl

/-- Inflation along `G ⟶ G ⧸ H` keeps the projections epimorphisms. -/
lemma epi_inflatedQuotientInvariants_map_projection_f
    (hK : ∀ {m' m : ℕ} (h : m' ≤ m) (q : ℕ),
      Epi ((smoothQuotientInvariants R H).map ((K.projection h).f q)))
    {m' m : ℕ} (h : m' ≤ m) (q : ℕ) :
    Epi ((smoothQuotientInvariants R H ⋙ Rep.resFunctor (QuotientGroup.mk' H)).map
      ((K.projection h).f q)) :=
  (Rep.epi_iff_surjective _).2
    ((Rep.epi_iff_surjective ((smoothQuotientInvariants R H).map ((K.projection h).f q))).1
      (hK h q))

/-- The inflation along `G ⟶ G ⧸ H` of the `H`-invariants system, as an `ℓ`-divisible system of
complexes of representations of `G`. -/
def inflatedQuotientInvariantsComplexes
    (hK : ∀ {m' m : ℕ} (h : m' ≤ m) (q : ℕ),
      Epi ((smoothQuotientInvariants R H).map ((K.projection h).f q))) :
    DivisibleSystem (CochainComplex (Rep.{uV} R G) ℕ) ℓ :=
  K.mapComplexes (smoothQuotientInvariants R H ⋙ Rep.resFunctor (QuotientGroup.mk' H))
    (K.epi_inflatedQuotientInvariants_map_projection_f H hK)

/-- The inclusion of the `H`-invariants into the underlying system, as a morphism of
`ℓ`-divisible systems of complexes of representations of `G`. For section complexes this is the
inclusion `G_m^•(U(ẽ)_F̄)^H ⊂ G_m^•(U(ẽ)_F̄)` of Harris 1999, p.305; whether it is a
quasi-isomorphism is not addressed. -/
def quotientInvariantsComplexesInclusion
    (hK : ∀ {m' m : ℕ} (h : m' ≤ m) (q : ℕ),
      Epi ((smoothQuotientInvariants R H).map ((K.projection h).f q))) :
    K.inflatedQuotientInvariantsComplexes H hK ⟶ K.toRepComplexes :=
  K.mapComplexesNatTrans (smoothQuotientInvariantsInclusion R H)
    (K.epi_inflatedQuotientInvariants_map_projection_f H hK) K.epi_toRep_map_projection_f

lemma quotientInvariantsComplexesInclusion_tower_app_f
    (hK : ∀ {m' m : ℕ} (h : m' ≤ m) (q : ℕ),
      Epi ((smoothQuotientInvariants R H).map ((K.projection h).f q)))
    (m : ℕᵒᵖ) (q : ℕ) :
    ((K.quotientInvariantsComplexesInclusion H hK).tower.app m).f q =
      Rep.ofHom ((SmoothRep.toRep.obj ((K.tower.obj m).X q)).ρ.quotientToInvariants_lift H) :=
  (Category.comp_id _)

end Smooth

section SmoothGodement

open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.Godement
  Langlands.Cohomology.SmoothGodement

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {X : Type u} [TopologicalSpace X] [MulAction G X]
  [ContinuousConstSMul G X] [HasStableNeighbourhoods G X] {ℓ : ℕ}
  (h : SmoothGodementZeroExactStatement R G X) (T : SmoothSheafDivisibleSystem R G X ℓ)
  (D : ℕ) (H : Subgroup G) [H.Normal]

/-- Harris's system `{G_m(U)^H}`: the `H`-invariants of the compact sections of the truncated
smooth Godement resolution system, as an `ℓ`-divisible system of finite-length complexes of
representations of `G ⧸ H`, given that the `H`-invariants of the compact sections of the
projections of `F^q`, `q ≤ D`, and of `R (D + 1)` are epimorphisms. -/
def smoothGodementTruncatedQuotientInvariantSectionsSystem
    (hterm : ∀ q ≤ D, ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi ((smoothSheafCompactSections R G X ⋙ smoothQuotientInvariants R H).map
        ((smoothGodementTermSystem h T q).projection hm)))
    (hres : ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi ((smoothSheafCompactSections R G X ⋙ smoothQuotientInvariants R H).map
        ((smoothGodementResidualSystem h T (D + 1)).projection hm))) :
    DivisibleSystem (CochainComplex (Rep.{u} R (G ⧸ H)) ℕ) ℓ :=
  haveI := h.1
  haveI := h.2.1
  haveI := h.2.2
  truncatedResolutionSectionsSystem (smoothZeroFunctor R G X) (smoothCoaugmentation R G X) T D
    (smoothSheafCompactSections R G X ⋙ smoothQuotientInvariants R H) hterm hres

end SmoothGodement

end DivisibleSystem

end Langlands.Cohomology
