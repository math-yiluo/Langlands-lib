import Langlands.Global.AdelicFunctoriality.CompletedRamification
import Langlands.Global.AdelicFunctoriality.Infinite
import Langlands.Global.AdelicFunctoriality.Norm
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.Group.Units

/-! # Extension-of-scalars inclusions of adeles, ideles and idele classes

For a finite extension `L / K` of number fields, the coordinate at a place of `L`
is the completed embedding applied to the coordinate at the place of `K` below it.
These maps are distinct from the norm maps in `Norm`.
-/

noncomputable section

namespace Langlands.Global.AdelicFunctoriality

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter
open scoped NumberField

universe u v

variable {K : Type u} {L : Type v} [Field K] [Field L]
  [NumberField K] [NumberField L] [Algebra K L]

/-- Every finite place of `L` lies over its restriction to `K`. -/
instance liesOver_under (q : HeightOneSpectrum (𝓞 L)) :
    q.asIdeal.LiesOver (q.under (𝓞 K)).asIdeal :=
  Ideal.over_under q.asIdeal

/-- Only finitely many finite places of `L` restrict to a given finite place of `K`. -/
theorem tendsto_under_cofinite :
    Tendsto (HeightOneSpectrum.under (𝓞 K) :
      HeightOneSpectrum (𝓞 L) → HeightOneSpectrum (𝓞 K)) cofinite cofinite := by
  apply Tendsto.cofinite_of_finite_preimage_singleton
  intro p
  refine (Set.finite_range (fun q : FinitePlacesAbove L p => q.1)).subset ?_
  intro q hq
  rw [Set.mem_preimage, Set.mem_singleton_iff] at hq
  subst hq
  exact ⟨⟨q, liesOver_under q⟩, rfl⟩

/-- The finite-adele inclusion: the coordinate at `q` is the completed embedding
of the coordinate at the place of `K` below `q`. -/
def finiteAdeleInclusion : FiniteAdeleRing (𝓞 K) K →+* FiniteAdeleRing (𝓞 L) L :=
  RestrictedProduct.mapAlongRingHom _ _ (HeightOneSpectrum.under (𝓞 K))
    tendsto_under_cofinite
    (fun q => FiniteExtension.completionMap (q.under (𝓞 K)) q)
    (Eventually.of_forall fun q x hx =>
      (FiniteExtension.completionMap_mem_integers_iff (q.under (𝓞 K)) q x).mpr hx)

@[simp] theorem finiteAdeleInclusion_apply (x : FiniteAdeleRing (𝓞 K) K)
    (q : HeightOneSpectrum (𝓞 L)) :
    finiteAdeleInclusion x q =
      FiniteExtension.completionMap (q.under (𝓞 K)) q (x (q.under (𝓞 K))) := rfl

theorem continuous_finiteAdeleInclusion :
    Continuous (finiteAdeleInclusion (K := K) (L := L)) :=
  RestrictedProduct.mapAlong_continuous _ _ (HeightOneSpectrum.under (𝓞 K))
    tendsto_under_cofinite
    (fun q => FiniteExtension.completionMap (q.under (𝓞 K)) q)
    (Eventually.of_forall fun q x hx =>
      (FiniteExtension.completionMap_mem_integers_iff (q.under (𝓞 K)) q x).mpr hx)
    (fun q => FiniteExtension.continuous_completionMap (q.under (𝓞 K)) q)

@[simp] theorem finiteAdeleInclusion_diagonal (x : K) :
    finiteAdeleInclusion (algebraMap K (FiniteAdeleRing (𝓞 K) K) x) =
      algebraMap L (FiniteAdeleRing (𝓞 L) L) (algebraMap K L x) := by
  apply FiniteAdeleRing.ext
  intro q
  exact FiniteExtension.completionMap_coe (q.under (𝓞 K)) q x

/-- The adele inclusion, with the infinite factor from `infiniteAdeleMap`. -/
def adeleInclusion : AdeleRing (𝓞 K) K →+* AdeleRing (𝓞 L) L :=
  RingHom.prodMap (infiniteAdeleMap (algebraMap K L)) finiteAdeleInclusion

@[simp] theorem adeleInclusion_infinite_apply (x : AdeleRing (𝓞 K) K)
    (p : InfinitePlace L) :
    (adeleInclusion x).1 p =
      infiniteCompletionMap (algebraMap K L) p (x.1 (p.comap (algebraMap K L))) := rfl

@[simp] theorem adeleInclusion_finite_apply (x : AdeleRing (𝓞 K) K)
    (q : HeightOneSpectrum (𝓞 L)) :
    (adeleInclusion x).2 q =
      FiniteExtension.completionMap (q.under (𝓞 K)) q (x.2 (q.under (𝓞 K))) := rfl

theorem continuous_adeleInclusion : Continuous (adeleInclusion (K := K) (L := L)) :=
  ((continuous_infiniteAdeleMap (algebraMap K L)).comp continuous_fst).prodMk
    (continuous_finiteAdeleInclusion.comp continuous_snd)

@[simp] theorem adeleInclusion_diagonal (x : K) :
    adeleInclusion (algebraMap K (AdeleRing (𝓞 K) K) x) =
      algebraMap L (AdeleRing (𝓞 L) L) (algebraMap K L x) :=
  Prod.ext (infiniteAdeleMap_diagonal (algebraMap K L) x) (finiteAdeleInclusion_diagonal x)

/-- The induced continuous homomorphism of idele groups. -/
def ideleInclusion : IdeleGroup (𝓞 K) K →ₜ* IdeleGroup (𝓞 L) L where
  __ := Units.map (adeleInclusion (K := K) (L := L)).toMonoidHom
  continuous_toFun := Continuous.units_map _ continuous_adeleInclusion

@[simp] theorem ideleInclusion_val (a : IdeleGroup (𝓞 K) K) :
    (ideleInclusion (K := K) (L := L) a : AdeleRing (𝓞 L) L) =
      adeleInclusion (a : AdeleRing (𝓞 K) K) := rfl

/-- Principal ideles go to principal ideles, by the field embedding itself. -/
@[simp] theorem ideleInclusion_diagonal (x : Kˣ) :
    ideleInclusion (IdeleGroup.unitEmbedding (𝓞 K) K x) =
      IdeleGroup.unitEmbedding (𝓞 L) L (Units.map (algebraMap K L).toMonoidHom x) := by
  apply Units.ext
  exact adeleInclusion_diagonal (x : K)

theorem ideleInclusion_principal :
    IdeleGroup.principalSubgroup (𝓞 K) K ≤
      (IdeleGroup.principalSubgroup (𝓞 L) L).comap
        (ideleInclusion (K := K) (L := L)).toMonoidHom := by
  rintro _ ⟨x, rfl⟩
  exact ⟨Units.map (algebraMap K L).toMonoidHom x, (ideleInclusion_diagonal x).symm⟩

/-- The induced continuous homomorphism of idele class groups `C_K → C_L`. -/
def ideleClassInclusion : IdeleClassGroup (𝓞 K) K →ₜ* IdeleClassGroup (𝓞 L) L where
  __ := QuotientGroup.map _ _ (ideleInclusion (K := K) (L := L)).toMonoidHom
    ideleInclusion_principal
  continuous_toFun := by
    apply (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
    exact QuotientGroup.continuous_mk.comp (ideleInclusion (K := K) (L := L)).continuous

@[simp] theorem ideleClassInclusion_mk (a : IdeleGroup (𝓞 K) K) :
    ideleClassInclusion (K := K) (L := L) (QuotientGroup.mk a) =
      QuotientGroup.mk (ideleInclusion a) := rfl

end Langlands.Global.AdelicFunctoriality
