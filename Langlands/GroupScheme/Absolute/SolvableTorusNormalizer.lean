import Langlands.GroupScheme.Absolute.SolvableTorusQuotientProof
import Langlands.GroupScheme.Absolute.SolvableMaximalTorusSemidirectOfSection
import Langlands.GroupScheme.Torus.UnipotentQuotientMono

/-! # Normalizing points of tori in connected solvable groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] [IsAlgClosed k]
  {H : GroupScheme (Spec (CommRingCat.of k))}
  [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left]
  {T : CommGroupScheme (Spec (CommRingCat.of k))} {f : T.toGrp ⟶ H}

/-- Every point of a smooth connected solvable affine group that normalizes a
closed torus centralizes that torus. -/
theorem IsTorus.mem_centralizerPoints_of_mem_normalizerPoints_of_isSolvable
    (hT : IsTorus T.toGrp) (hH : IsSolvableGroupScheme H) (hf : IsClosedSubgroup f)
    (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X)
    (hn : n ∈ normalizerPoints f) : n ∈ centralizerPoints f := by
  obtain ⟨U, D, i, q, hi, hUs, hUc, hU, hnU, hq, hD⟩ :=
    solvableTorusQuotient k H hH
  have : IsAffineHom U.X.hom := hi.isAffineHom
  have : LocallyOfFiniteType U.X.hom := hi.locallyOfFiniteType
  have : Mono (f ≫ q).hom.hom :=
    hU.mono_torus_quotient unipotentClosedSubgroup hT i f hf q hq.2.2.2.le
  have : Mono (f ≫ q) :=
    (Grp.forget _).mono_of_mono_map (inferInstance : Mono (f ≫ q).hom.hom)
  obtain ⟨σ, hσ⟩ := hn
  change f ≫ (H.innerIso n).hom = CommGroupScheme.groupHom σ.hom ≫ f at hσ
  have hσq : (𝟙 T.toGrp) ≫ (f ≫ q) =
      CommGroupScheme.groupHom σ.hom ≫ (f ≫ q) := by
    rw [Category.id_comp, ← Category.assoc, ← hσ, Category.assoc,
      innerIso_hom_comp_of_isSplitTorus hD q n]
  have hσid : CommGroupScheme.groupHom σ.hom = 𝟙 T.toGrp :=
    ((cancel_mono (f ≫ q)).mp hσq).symm
  apply (mem_centralizerPoints f).mpr
  rw [hσ, hσid, Category.id_comp]

/-- In particular, normalizing points of a maximal torus in a smooth connected
solvable affine group centralize it. -/
theorem IsMaximalTorus.mem_centralizerPoints_of_mem_normalizerPoints_of_isSolvable
    (hf : IsMaximalTorus f) (hH : IsSolvableGroupScheme H)
    (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X)
    (hn : n ∈ normalizerPoints f) : n ∈ centralizerPoints f :=
  hf.1.mem_centralizerPoints_of_mem_normalizerPoints_of_isSolvable hH hf.2.1 n hn

end Langlands.GroupScheme
