/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Mathlib.AlgebraicGeometry.Restrict
import WeilConjectures.AlgebraicGeometry.FlatModelFiniteFreeTruncation
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- Construct a local finite-free model and a compatible quasi-isomorphism factorization.
Source: Stacks Project, Tags 064U, 0653, 00NX, 06YD and 06YJ.
Proof: restrict to an affine neighbourhood of t and set M = coker(Q^{-1} → Q^0).
The finite-free terms of Q are quasi-coherent, hence so is M, and M is finitely
presented. At each stalk, C is bounded and flat in [0,d], so it has Tor amplitude
[0,d]. The bounded-above free complex Q is K-flat at each stalk, and its
quasi-isomorphism to C implies negative tensor cohomology vanishes. Tag 0653
then gives flatness of M at every stalk. Thus the affine module associated to M
is finitely presented and flat, hence finite projective by Tag 00NX. Shrink
around t until M is finite free. No quasi-coherence of C is assumed.
Define P by the quotient truncation of Q: zero in negative degrees, M in degree
zero, and Q in positive degrees. It vanishes above d and all terms are finite free.
The quotient Q → P is a quasi-isomorphism because Q has no negative cohomology.
Since C^{-1} = 0, the chain map e kills the image of Q^{-1} → Q^0 and factors
through P. This factor is a quasi-isomorphism by two-out-of-three. Open restriction
is exact, so the same argument and comparison hold on the shrunken neighbourhood.
Retain the quotient map from the restricted Q to P as eQ. It is a
quasi-isomorphism and eQ ≫ eP equals the restriction of e, by the cokernel
universal property in degree zero and identity maps in positive degrees.
The witnesses are constructed simultaneously; no assertion concerns an arbitrary P.
(blueprint: lem-pc-flat-model-finite-free-quasi-iso). -/
theorem exists_local_finiteFree_quasiIso {T : Scheme.{u}} (U : T.Opens)
    (C Q : CochainComplex U.toScheme.Modules ℤ) (d : ℕ)
    (hCge : C.IsStrictlyGE 0) (hCle : C.IsStrictlyLE d)
    (hCflat : ∀ n : ℤ, (C.X n).IsFlatOver (𝟙 U.toScheme))
    (hQle : Q.IsStrictlyLE d)
    (hQfree : ∀ n : ℤ, ∃ r : ℕ,
      Nonempty (Q.X n ≅ SheafOfModules.free
        (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin r))))
    (e : Q ⟶ C) (he : QuasiIso e) (t : T) (ht : t ∈ U) :
    ∃ (V : T.Opens) (hVU : V ≤ U) (P : CochainComplex V.toScheme.Modules ℤ),
      (t ∈ V ∧ P.IsStrictlyGE 0 ∧ P.IsStrictlyLE d ∧
        (∀ n : ℤ, ∃ r : ℕ,
          Nonempty (P.X n ≅ SheafOfModules.free
            (R := V.toScheme.ringCatSheaf) (ULift.{u} (Fin r))))) ∧
      ∃ (eQ : ((Modules.pullback (T.homOfLE hVU)).mapHomologicalComplex _).obj Q ⟶ P)
        (eP : P ⟶ ((Modules.pullback (T.homOfLE hVU)).mapHomologicalComplex _).obj C),
        QuasiIso eQ ∧ QuasiIso eP ∧
          eQ ≫ eP = ((Modules.pullback (T.homOfLE hVU)).mapHomologicalComplex _).map e := by
  obtain ⟨V, hVU, htV, r, ⟨hzero⟩⟩ :=
    exists_local_finiteFree_truncation_zero U C Q d hCge hCle hCflat hQle hQfree e he t ht
  let f := T.homOfLE hVU
  let F := (Modules.pullback f).mapHomologicalComplex (ComplexShape.up ℤ)
  let QV : CochainComplex V.toScheme.Modules ℤ := F.obj Q
  let CV : CochainComplex V.toScheme.Modules ℤ := F.obj C
  let P := QV.truncGE 0
  have : PreservesFiniteLimits (Modules.pullback f) :=
    preservesFiniteLimits_of_natIso (restrictFunctorIsoPullback f)
  have : QuasiIso e := he
  have : C.IsStrictlyGE 0 := hCge
  have : Q.IsStrictlyLE (d : ℤ) := hQle
  have : CV.IsStrictlyGE 0 := inferInstance
  have : QV.IsStrictlyLE (d : ℤ) := inferInstance
  have : QuasiIso (F.map e) := inferInstance
  have : QV.IsGE 0 := (HomologicalComplex.isSupported_iff_of_quasiIso (F.map e)
    (ComplexShape.embeddingUpIntGE 0)).mpr inferInstance
  let q := QV.πTruncGE 0
  let p := CochainComplex.truncGEMap (F.map e) 0 ≫ inv (CV.πTruncGE 0)
  have hp : QuasiIso (CochainComplex.truncGEMap (F.map e) 0) := by
    rw [CochainComplex.quasiIso_truncGEMap_iff]
    intro i hi
    infer_instance
  refine ⟨V, hVU, P, ⟨htV, inferInstance, inferInstance, ?_⟩,
    q, p, inferInstance, inferInstance, ?_⟩
  · intro n
    obtain hn | rfl | hn := lt_trichotomy n 0
    · have hz : IsZero (SheafOfModules.free
          (R := V.toScheme.ringCatSheaf) (ULift.{u} (Fin 0))) := by
        apply (IsZero.iff_id_eq_zero _).mpr
        apply (SheafOfModules.freeHomEquiv _).injective
        funext j
        exact Fin.elim0 j.down
      exact ⟨0, ⟨(P.isZero_of_isStrictlyGE 0 n hn).iso hz⟩⟩
    · exact ⟨r, ⟨hzero⟩⟩
    · obtain ⟨s, ⟨hs⟩⟩ := hQfree n
      exact ⟨s, ⟨QV.truncGEXIso 0 n hn ≪≫
        (Modules.pullback f).mapIso hs ≪≫ pullbackFreeIso f _⟩⟩
  · dsimp [q, p]
    rw [← Category.assoc, CochainComplex.πTruncGE_naturality]
    simp [F, f]

end AlgebraicGeometry.Scheme.Modules
