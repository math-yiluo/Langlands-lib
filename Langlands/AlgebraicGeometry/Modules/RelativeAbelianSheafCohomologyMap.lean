import Langlands.AlgebraicGeometry.Modules.RelativeAbelianSheafComparison
import Langlands.AlgebraicGeometry.Modules.AbelianSheafCohomologyNaturality
import Langlands.AlgebraicGeometry.Modules.ClosedImmersionCohomologyMap
import Langlands.AlgebraicGeometry.Picard.UnitSheafPushforwardDerived

/-! # Actual relative cohomology maps and Ext-defined sheaf cohomology -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Cohomology Langlands.Cohomology.AcyclicResolution

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 2048
set_option maxHeartbeats 800000

namespace Langlands.AlgebraicGeometry.Modules.AbelianSheafComparison

open PushforwardInjectiveAcyclic
open Picard.UnitSheafPushforward

variable {X Y : Scheme.{u}} {R : CommRingCat.{u}} (f : X ⟶ Spec R)

/-- The published actual module-cohomology comparison with scalars restricted
along the specified structure morphism. -/
def relativeHAddEquiv (M : X.Modules) (n : ℕ) :
    Sheaf.H.{u} ((toAbSheaf X).obj M) n ≃+
      (DerivedSections.relativeCohomology f n).obj M :=
  (HAddEquiv X M n).trans
    (((DerivedSections.relativeCohomologyRestrictScalarsIso f n).app M).toLinearEquiv.toAddEquiv)

/-- The relative additive comparison recovers the unchanged derived-sections
comparison after canonical forgetting of scalars. -/
lemma relativeCohomologyIso_relativeHAddEquiv (M : X.Modules) (n : ℕ)
    (x : Sheaf.H.{u} ((toAbSheaf X).obj M) n) :
    (relativeCohomologyIso f M n).hom (relativeHAddEquiv f M n x) =
      AbelianSheafDerivedSections.HAddEquiv X.toTopCat ((toAbSheaf X).obj M) n x := by
  have h := ConcreteCategory.congr_hom (relativeCohomologyIso_restrictScalars f M n)
    (HAddEquiv X M n x)
  change (relativeCohomologyIso f M n).hom (relativeHAddEquiv f M n x) = _ at h
  rw [h]
  change (cohomologyIso X M n).hom ((cohomologyIso X M n).inv _) = _
  exact (cohomologyIso X M n).inv_hom_id_apply _

/-- Restricting the target scalar action preserves coefficient naturality of
the actual additive cohomology comparison. -/
lemma relativeHAddEquiv_naturality {M N : X.Modules} (a : M ⟶ N) (n : ℕ)
    (x : Sheaf.H.{u} ((toAbSheaf X).obj M) n) :
    (DerivedSections.relativeCohomology f n).map a (relativeHAddEquiv f M n x) =
      relativeHAddEquiv f N n (Sheaf.H.map ((toAbSheaf X).map a) n x) := by
  apply (relativeCohomologyIso f N n).addCommGroupIsoToAddEquiv.injective
  have hn := ConcreteCategory.congr_hom (relativeCohomologyIso_hom_naturality f a n)
    (relativeHAddEquiv f M n x)
  change (relativeCohomologyIso f N n).hom
      ((DerivedSections.relativeCohomology f n).map a (relativeHAddEquiv f M n x)) =
    ((AbelianSheafDerivedSections.globalSections X.toTopCat).rightDerived n).map
      ((toAbSheaf X).map a) ((relativeCohomologyIso f M n).hom
        (relativeHAddEquiv f M n x)) at hn
  change (relativeCohomologyIso f N n).hom _ = (relativeCohomologyIso f N n).hom _
  rw [hn, relativeCohomologyIso_relativeHAddEquiv,
    relativeCohomologyIso_relativeHAddEquiv]
  exact (AbelianSheafDerivedSections.HAddEquiv_naturality X.toTopCat
    ((toAbSheaf X).map a) n x).symm

/-- Changing the affine base ring preserves the actual additive comparison. -/
lemma relativeHAddEquiv_baseRing {S : CommRingCat.{u}} (φ : R ⟶ S)
    (f' : X ⟶ Spec S) (w : f = f' ≫ Spec.map φ) (M : X.Modules) (n : ℕ)
    (x : Sheaf.H.{u} ((toAbSheaf X).obj M) n) :
    (DerivedSections.relativeCohomologyBaseRingIso φ f f' w n).hom.app M
      (relativeHAddEquiv f M n x) = relativeHAddEquiv f' M n x := by
  apply (relativeCohomologyIso f' M n).addCommGroupIsoToAddEquiv.injective
  have hb := ConcreteCategory.congr_hom
    (relativeCohomologyIso_baseRing f φ f' w M n) (relativeHAddEquiv f M n x)
  change (relativeCohomologyIso f' M n).hom
      ((DerivedSections.relativeCohomologyBaseRingIso φ f f' w n).hom.app M
        (relativeHAddEquiv f M n x)) =
    (relativeCohomologyIso f M n).hom (relativeHAddEquiv f M n x) at hb
  change (relativeCohomologyIso f' M n).hom _ = (relativeCohomologyIso f' M n).hom _
  rw [hb, relativeCohomologyIso_relativeHAddEquiv,
    relativeCohomologyIso_relativeHAddEquiv]

variable (h : X ⟶ Y) (g : Y ⟶ Spec R) [IsClosedImmersion h] [IsIso h.base]

local instance : (TopCat.Sheaf.pushforward AddCommGrpCat.{u} h.base).IsEquivalence :=
  (sheafPushforwardEquivalence (C := AddCommGrpCat.{u}) (asIso h.base)).isEquivalence_functor

local instance : (TopCat.Sheaf.pushforward AddCommGrpCat.{u} h.base).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The relative module pushforward comparison has the actual canonical
abelian derived-sections comparison as its underlying map. -/
lemma relativeCohomologyIso_pushforward_apply (M : X.Modules) (n : ℕ)
    (x : (DerivedSections.relativeCohomology (h ≫ g) n).obj M) :
    (relativeCohomologyIso g ((Scheme.Modules.pushforward h).obj M) n).hom
      ((DerivedSections.pushforwardCohomologyIso h g M
        (fun q => closedImmersionHigherDirectImageVanishing X Y h inferInstance M q) n).hom x) =
    pushforwardDerivedComparison (asIso h.base) ((toAbSheaf X).obj M) n
      ((relativeCohomologyIso (h ≫ g) M n).hom x) := by
  have hp := relativeCohomologyIso_pushforward h g M n
  have hi : (pushforwardForgetIso h).hom.app M = 𝟙 _ := rfl
  erw [hi, CategoryTheory.Functor.map_id, Category.comp_id] at hp
  have hc : compComparison (F := TopCat.Sheaf.pushforward AddCommGrpCat.{u} h.base)
      (AbelianSheafDerivedSections.globalSections Y.toTopCat)
      (abelianPushforwardSectionsIso h) ((toAbSheaf X).obj M)
      (isZero_rightDerived_abelianPushforward h ((toAbSheaf X).obj M)) n =
      pushforwardDerivedComparison (asIso h.base) ((toAbSheaf X).obj M) n := rfl
  rw [hc] at hp
  have hv := ConcreteCategory.congr_hom hp x
  change (relativeCohomologyIso g ((Scheme.Modules.pushforward h).obj M) n).hom
      (DerivedSections.pushforwardComparison h g M
        (fun q => closedImmersionHigherDirectImageVanishing X Y h inferInstance M q) n x) =
    pushforwardDerivedComparison (asIso h.base) ((toAbSheaf X).obj M) n
      ((relativeCohomologyIso (h ≫ g) M n).hom x) at hv
  exact hv

/-- The actual Ext-defined pushforward agrees with the existing relative
module pushforward isomorphism under the unchanged scalar restriction. -/
lemma relativeHAddEquiv_pushforward (M : X.Modules) (n : ℕ)
    (a : Sheaf.H.{u} ((toAbSheaf Y).obj ((Scheme.Modules.pushforward h).obj M)) n) :
    (DerivedSections.pushforwardCohomologyIso h g M
        (fun q => closedImmersionHigherDirectImageVanishing X Y h inferInstance M q) n).hom
      (relativeHAddEquiv (h ≫ g) M n
        (cohomologyPushforwardEquiv (asIso h.base) ((toAbSheaf X).obj M) n a)) =
      relativeHAddEquiv g ((Scheme.Modules.pushforward h).obj M) n a := by
  apply (relativeCohomologyIso g ((Scheme.Modules.pushforward h).obj M) n).addCommGroupIsoToAddEquiv.injective
  change (relativeCohomologyIso g ((Scheme.Modules.pushforward h).obj M) n).hom _ =
    (relativeCohomologyIso g ((Scheme.Modules.pushforward h).obj M) n).hom _
  rw [relativeCohomologyIso_pushforward_apply,
    relativeCohomologyIso_relativeHAddEquiv,
    relativeCohomologyIso_relativeHAddEquiv]
  exact cohomologyPushforwardEquiv_HAddEquiv (asIso h.base)
    (F := (toAbSheaf X).obj M) n a

/-- The inverse relative module comparison is the forward Ext-defined
pushforward on actual underlying abelian sheaves. -/
lemma relativeHAddEquiv_pushforward_inv (M : X.Modules) (n : ℕ)
    (a : Sheaf.H.{u} ((toAbSheaf Y).obj ((Scheme.Modules.pushforward h).obj M)) n) :
    (DerivedSections.pushforwardCohomologyIso h g M
        (fun q => closedImmersionHigherDirectImageVanishing X Y h inferInstance M q) n).inv
      (relativeHAddEquiv g ((Scheme.Modules.pushforward h).obj M) n a) =
    relativeHAddEquiv (h ≫ g) M n
      (cohomologyPushforwardEquiv (asIso h.base) ((toAbSheaf X).obj M) n a) := by
  apply (DerivedSections.pushforwardCohomologyIso h g M
    (fun q => closedImmersionHigherDirectImageVanishing X Y h inferInstance M q) n).toLinearEquiv.injective
  change (DerivedSections.pushforwardCohomologyIso h g M _ n).hom
      ((DerivedSections.pushforwardCohomologyIso h g M _ n).inv _) = _
  rw [Iso.inv_hom_id_apply]
  exact (relativeHAddEquiv_pushforward h g M n a).symm

/-- The canonical closed-immersion cohomology map agrees with the actual
Ext-defined map, retaining coefficient maps and the specified affine-base square. -/
lemma relativeHAddEquiv_closedImmersionCohomologyMap {S : CommRingCat.{u}}
    (φ : R ⟶ S) (g' : X ⟶ Spec S) (w : h ≫ g = g' ≫ Spec.map φ)
    {M : Y.Modules} {N : X.Modules}
    (a : M ⟶ (Scheme.Modules.pushforward h).obj N) (n : ℕ)
    (x : Sheaf.H.{u} ((toAbSheaf Y).obj M) n) :
    DerivedSections.closedImmersionCohomologyMap φ g g' h w a n
      (relativeHAddEquiv g M n x) =
    relativeHAddEquiv g' N n
      (cohomologyPushforwardEquiv (asIso h.base) ((toAbSheaf X).obj N) n
        (Sheaf.H.map ((toAbSheaf Y).map a) n x)) := by
  change (DerivedSections.relativeCohomologyBaseRingIso φ (h ≫ g) g' w n).hom.app N
      ((DerivedSections.pushforwardCohomologyIso h g N _ n).inv
        ((DerivedSections.relativeCohomology g n).map a (relativeHAddEquiv g M n x))) = _
  rw [relativeHAddEquiv_naturality, relativeHAddEquiv_pushforward_inv,
    relativeHAddEquiv_baseRing]

end Langlands.AlgebraicGeometry.Modules.AbelianSheafComparison
