/-
Copyright (c) 2024 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Salvatore Mercuri, Ruben Van de Velde, Matthew Jasper, Bryan Wang Peng Jun,
Yaël Dillies

Modified by Worker 50 (2026): adapt the scoped finite-adele algebra construction
from Imperial FLT, commit 923d45174c500aa1d994ba973bac38ea39eacbf7,
FLT/NumberField/AdeleRing.lean:349-370. Use the Library's finiteAdeleInclusion
and completion algebra, retain independent universes, and add scalar coherence.
The upstream license is retained at licenses/ImperialCollegeLondon-FLT/LICENSE.
-/
import Langlands.Global.AdelicFunctoriality.Inclusion

/-! # Scoped scalar extension between finite adele rings

Open `Langlands.Global.AdelicFunctoriality.FiniteAdeleExtension` as a scope to
use the finite-adele algebra induced by `finiteAdeleInclusion`.
-/

noncomputable section

namespace Langlands.Global.AdelicFunctoriality.FiniteAdeleExtension

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField FiniteExtension

universe u v

variable {K : Type u} {L : Type v} [Field K] [Field L]
  [NumberField K] [NumberField L] [Algebra K L]

/-- The adelic algebra induced by the completed embeddings at the finite places. -/
scoped instance instAlgebra :
    Algebra (FiniteAdeleRing (𝓞 K) K) (FiniteAdeleRing (𝓞 L) L) :=
  (finiteAdeleInclusion (K := K) (L := L)).toAlgebra

/-- The new scalar map is exactly the existing finite-adele inclusion. -/
theorem algebraMap_eq :
    algebraMap (FiniteAdeleRing (𝓞 K) K) (FiniteAdeleRing (𝓞 L) L) =
      finiteAdeleInclusion := rfl

@[simp] theorem algebraMap_apply (x : FiniteAdeleRing (𝓞 K) K)
    (q : HeightOneSpectrum (𝓞 L)) :
    algebraMap (FiniteAdeleRing (𝓞 K) K) (FiniteAdeleRing (𝓞 L) L) x q =
      FiniteExtension.completionMap (q.under (𝓞 K)) q (x (q.under (𝓞 K))) := rfl

@[simp] theorem smul_apply (x : FiniteAdeleRing (𝓞 K) K)
    (y : FiniteAdeleRing (𝓞 L) L) (q : HeightOneSpectrum (𝓞 L)) :
    (x • y) q =
      FiniteExtension.completionMap (q.under (𝓞 K)) q (x (q.under (𝓞 K))) * y q := rfl

/-- The coordinate action uses the existing scoped local-completion algebra. -/
theorem smul_apply_eq_local_smul (x : FiniteAdeleRing (𝓞 K) K)
    (y : FiniteAdeleRing (𝓞 L) L) (q : HeightOneSpectrum (𝓞 L)) :
    (x • y) q = x (q.under (𝓞 K)) • y q := rfl

@[simp] theorem algebraMap_diagonal (k : K) :
    algebraMap (FiniteAdeleRing (𝓞 K) K) (FiniteAdeleRing (𝓞 L) L)
      (algebraMap K (FiniteAdeleRing (𝓞 K) K) k) =
        algebraMap L (FiniteAdeleRing (𝓞 L) L) (algebraMap K L k) :=
  finiteAdeleInclusion_diagonal k

/-- The two routes from the coefficient field to the target finite adeles agree. -/
theorem algebraMap_comp_diagonal :
    (algebraMap (FiniteAdeleRing (𝓞 K) K) (FiniteAdeleRing (𝓞 L) L)).comp
      (algebraMap K (FiniteAdeleRing (𝓞 K) K)) =
        (algebraMap L (FiniteAdeleRing (𝓞 L) L)).comp (algebraMap K L) :=
  RingHom.ext algebraMap_diagonal

@[simp] theorem diagonal_smul (k : K) (y : FiniteAdeleRing (𝓞 L) L) :
    (algebraMap K (FiniteAdeleRing (𝓞 K) K) k) • y = (algebraMap K L k) • y := by
  rw [Algebra.smul_def, algebraMap_diagonal, Algebra.smul_def]

section CoefficientScalars

variable [Algebra K (FiniteAdeleRing (𝓞 L) L)]
  [IsScalarTower K L (FiniteAdeleRing (𝓞 L) L)]

/-- Any coefficient action compatible with the `L` diagonal is compatible with
restriction along the finite-adele inclusion. No new coefficient action is chosen. -/
scoped instance instIsScalarTower :
    IsScalarTower K (FiniteAdeleRing (𝓞 K) K) (FiniteAdeleRing (𝓞 L) L) :=
  .of_algebraMap_eq fun k => by
    rw [algebraMap_diagonal]
    exact IsScalarTower.algebraMap_apply K L (FiniteAdeleRing (𝓞 L) L) k

/-- The inclusion as a `K`-algebra homomorphism for compatible coefficient scalars. -/
def inclusionAlgHom : FiniteAdeleRing (𝓞 K) K →ₐ[K] FiniteAdeleRing (𝓞 L) L where
  __ := finiteAdeleInclusion
  commutes' k := (finiteAdeleInclusion_diagonal k).trans
    (IsScalarTower.algebraMap_apply K L (FiniteAdeleRing (𝓞 L) L) k).symm

end CoefficientScalars

end Langlands.Global.AdelicFunctoriality.FiniteAdeleExtension
