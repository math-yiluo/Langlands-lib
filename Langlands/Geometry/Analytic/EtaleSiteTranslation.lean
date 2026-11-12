import Langlands.Geometry.Analytic.EtaleSite
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology

/-! # Translation of the étale site along isomorphisms is continuous and cocontinuous -/

noncomputable section

universe u v

open CategoryTheory

namespace Langlands.Analytic

/-- Let `e : C ≌ D` be an equivalence and `J`, `K` precoverages. If the image under `e.inverse`
of every `K`-covering is a `J`-covering, then `e.functor` is cocontinuous for the generated
Grothendieck topologies. -/
theorem isCocontinuous_toGrothendieck_of_equivalence {C D : Type*} [Category* C] [Category* D]
    (e : C ≌ D) (J : Precoverage C) (K : Precoverage D)
    (hK : ∀ {V : D} {R : Presieve V}, R ∈ K V → R.map e.inverse ∈ J (e.inverse.obj V)) :
    e.functor.IsCocontinuous J.toGrothendieck K.toGrothendieck where
  cover_lift {U S} hS := by
    have hle : K.toGrothendieck ≤ e.inverse.restrictedTopology J.toGrothendieck := by
      rw [Precoverage.toGrothendieck_le_iff_le_toPrecoverage]
      intro V R hR
      rw [GrothendieckTopology.mem_toPrecoverage_iff, Functor.mem_restrictedTopology_iff,
        ← Sieve.generate_map_eq_functorPushforward]
      exact Precoverage.generate_mem_toGrothendieck (hK hR)
    have h1 := hle _ hS
    rw [Functor.mem_restrictedTopology_iff, Sieve.functorPushforward_inverse] at h1
    have h2 := J.toGrothendieck.pullback_stable (e.unit.app U) h1
    have heq : Sieve.functorPullback e.functor S = Sieve.pullback (e.unit.app U)
        (Sieve.functorPullback e.functor (Sieve.pullback (e.counit.app (e.functor.obj U)) S)) := by
      ext W f
      simp
    rw [heq]
    exact h2

namespace SaturatedAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace EtaleSite

variable {X Y : LocalizedCategory.{u, v, v} (K := K)}

/-- Translation backwards along `e : X ≅ Y` does not change underlying points. -/
theorem etalePrecoverage_eq_comap_translate_inverse (e : X ≅ Y) :
    etalePrecoverage Y = (etalePrecoverage X).comap (translate e).inverse :=
  Precoverage.comap_comp (translate e).inverse (points X) Types.jointlySurjectivePrecoverage

theorem etalePrecoverage_eq_comap_translate_functor (e : X ≅ Y) :
    etalePrecoverage X = (etalePrecoverage Y).comap (translate e).functor :=
  Precoverage.comap_comp (translate e).functor (points Y) Types.jointlySurjectivePrecoverage

/-- Translation along an isomorphism is cocontinuous for the étale topologies. -/
instance isCocontinuous_translate_functor (e : X ≅ Y) :
    (translate e).functor.IsCocontinuous (etaleTopology X) (etaleTopology Y) :=
  isCocontinuous_toGrothendieck_of_equivalence (translate e) _ _ fun {V R} hR => by
    rw [etalePrecoverage_eq_comap_translate_inverse e] at hR
    exact (Precoverage.mem_comap_iff).1 hR

/-- The inverse of translation is cocontinuous for the étale topologies. -/
instance isCocontinuous_translate_inverse (e : X ≅ Y) :
    (translate e).inverse.IsCocontinuous (etaleTopology Y) (etaleTopology X) :=
  isCocontinuous_toGrothendieck_of_equivalence (translate e).symm _ _ fun {V R} hR => by
    rw [etalePrecoverage_eq_comap_translate_functor e] at hR
    exact (Precoverage.mem_comap_iff).1 hR

/-- Translation along an isomorphism identifies the étale sites: it is a dense subsite
equivalence. -/
instance isDenseSubsite_translate_functor (e : X ≅ Y) :
    (translate e).functor.IsDenseSubsite (etaleTopology X) (etaleTopology Y) :=
  Equivalence.isDenseSubsite_functor_of_isCocontinuous _ _ (translate e)

/-- The inverse of translation is a dense subsite equivalence as well. -/
instance isDenseSubsite_translate_inverse (e : X ≅ Y) :
    (translate e).inverse.IsDenseSubsite (etaleTopology Y) (etaleTopology X) :=
  Equivalence.isDenseSubsite_inverse_of_isCocontinuous _ _ (translate e)

/-- Translation along an isomorphism is continuous for the étale topologies. -/
theorem isContinuous_translate_functor (e : X ≅ Y) :
    (translate e).functor.IsContinuous (etaleTopology X) (etaleTopology Y) :=
  inferInstance

/-- Translation along `e : X ≅ Y` identifies sheaves on the étale sites of `X` and `Y`, with
values in any category. -/
def sheafTranslate (e : X ≅ Y) (A : Type*) [Category* A] :
    Sheaf (etaleTopology X) A ≌ Sheaf (etaleTopology Y) A :=
  Equivalence.sheafCongr _ _ (translate e) A

end EtaleSite

end SaturatedAtlasPresentation

end Langlands.Analytic
