import Langlands.GroupScheme.AffineCorepresented
import Langlands.GroupScheme.CorepresentedClosedSubgroup

/-! # Smoothness of cut-out subgroup schemes from infinitesimal lifting

For a group functor `F` on commutative `R`-algebras corepresented by `B`, and subgroups `H A`
cut out by an ideal `J`, the quotient `B ⧸ J` is formally smooth over `R` as soon as points of
`H` lift along square-zero extensions. If moreover `B ⧸ J` is of finite presentation, the cut-out
group scheme `Spec (B ⧸ J)` is smooth over `Spec R`.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry

namespace Langlands.GroupScheme

namespace Corepresented

variable {R : CommRingCat.{u}} {F : CommAlgCat.{u} R ⥤ GrpCat.{u}} {B : CommAlgCat.{u} R}
  {e : (F ⋙ forget GrpCat).CorepresentableBy B}

/-- The reduction map `C ⟶ C ⧸ N` in `CommAlgCat R`. -/
abbrev reduction (C : CommAlgCat.{u} R) (N : Ideal C) : C ⟶ CommAlgCat.of R (C ⧸ N) :=
  CommAlgCat.ofHom (Ideal.Quotient.mkₐ R N)

/-- A family of subgroups has the infinitesimal lifting property when every point over a
square-zero quotient `C ⧸ N` lifts to a point over `C`. -/
def HasSquareZeroLifting (H : ∀ A : CommAlgCat.{u} R, Subgroup (F.obj A)) : Prop :=
  ∀ (C : CommAlgCat.{u} R) (N : Ideal C), N ^ 2 = ⊥ →
    ∀ x ∈ H (CommAlgCat.of R (C ⧸ N)), ∃ y ∈ H C, F.map (reduction C N) y = x

variable {H : ∀ A : CommAlgCat.{u} R, Subgroup (F.obj A)} {J : Ideal B}

/-- **Formal smoothness from lifting.** If the points of a family cut out by `J` lift along
square-zero extensions, then `B ⧸ J` is formally smooth over `R`. -/
theorem formallySmooth_of_hasSquareZeroLifting (hJ : IsCutOutBy e H J)
    (hH : HasSquareZeroLifting H) : Algebra.FormallySmooth R (B ⧸ J) := by
  refine Algebra.FormallySmooth.of_comp_surjective fun C _ _ N hN g => ?_
  let C' : CommAlgCat.{u} R := CommAlgCat.of R C
  let x : F.obj (CommAlgCat.of R (C' ⧸ N)) := e.homEquiv (quotientMap J ≫ CommAlgCat.ofHom g)
  have hx : x ∈ H (CommAlgCat.of R (C' ⧸ N)) := by
    rw [hJ]
    intro b hb
    rw [Equiv.symm_apply_apply]
    change g (Ideal.Quotient.mk J b) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hb, map_zero]
  obtain ⟨y, hy, hyx⟩ := hH C' N hN x hx
  have hyJ := (hJ C' y).1 hy
  refine ⟨Ideal.Quotient.liftₐ J (e.homEquiv.symm y).hom hyJ, ?_⟩
  apply Ideal.Quotient.algHom_ext
  ext b
  change Ideal.Quotient.mk N ((e.homEquiv.symm y).hom b) = g (Ideal.Quotient.mk J b)
  have h := congrArg (fun φ => φ.hom b) (e.homEquiv_symm_comp y (reduction C' N))
  have h' : (e.homEquiv.symm y ≫ reduction C' N).hom b = (e.homEquiv.symm x).hom b := by
    rw [← hyx]
    exact h
  rw [Equiv.symm_apply_apply] at h'
  exact h'

/-- **Smoothness of cut-out group schemes.** If `B ⧸ J` is smooth over `R`, the closed subgroup
scheme `Spec (B ⧸ J)` cut out by `J` is smooth over `Spec R`. -/
theorem smooth_cutGroupScheme (hJ : IsCutOutBy e H J) [Algebra.Smooth R (B ⧸ J)] :
    Smooth (cutGroupScheme hJ).X.hom := by
  have h : Smooth (Spec.map (CommRingCat.ofHom (algebraMap R (B ⧸ J)))) :=
    (HasRingHomProperty.Spec_iff (P := @Smooth)).2 (RingHom.smooth_algebraMap.2 inferInstance)
  exact h

/-- Over a noetherian base, a quotient of a finite-type algebra is of finite presentation. -/
theorem finitePresentation_quotient [IsNoetherianRing R] [Algebra.FiniteType R B] (J : Ideal B) :
    Algebra.FinitePresentation R (B ⧸ J) :=
  Algebra.FinitePresentation.of_finiteType.1 inferInstance

/-- Smoothness of a corepresented group scheme over `Spec R` is smoothness of its coordinate
algebra. -/
theorem smooth_groupScheme_iff : Smooth (groupScheme F e).X.hom ↔ Algebra.Smooth R B :=
  (HasRingHomProperty.Spec_iff (P := @Smooth)
    (φ := CommRingCat.ofHom (algebraMap R B))).trans RingHom.smooth_algebraMap

end Corepresented

namespace AffineCoordinates

variable {R : CommRingCat.{u}} (G : GroupScheme (Spec R)) [IsAffine G.X.left]

/-- The coordinate algebra of a smooth affine group scheme is smooth. -/
theorem smooth_algebra (hG : Smooth G.X.hom) : Algebra.Smooth R (algebra G) := by
  rw [← Corepresented.smooth_groupScheme_iff (e := corepresentation G)]
  have : IsIso (groupSchemeIso G).hom.hom.hom.left :=
    (inferInstance : IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso
      (groupSchemeIso G))).hom)
  rw [← Over.w (groupSchemeIso G).hom.hom.hom]
  have := hG
  infer_instance

end AffineCoordinates

end Langlands.GroupScheme
