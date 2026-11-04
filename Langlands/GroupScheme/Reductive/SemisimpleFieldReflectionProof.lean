import Langlands.GroupScheme.Reductive.SemisimpleFieldReflectionStatement
import Langlands.GroupScheme.Reductive.FiniteCenterReflection
import Langlands.GroupScheme.Reductive.GroundFieldRadical
import Langlands.GroupScheme.Rational.UnipotentRadicalProperties
import Langlands.AbelianScheme.Tate.BaseChangeCoherence

/-! # Reflection of semisimplicity under arbitrary field extension -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- For an affine group, triviality of the unipotent radical after a field extension
implies it over the original field. -/
theorem HasTrivialUnipotentRadical.of_fieldExtension
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (h : HasTrivialUnipotentRadical
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G)) :
    HasTrivialUnipotentRadical G := by
  intro H i hi hs hc hu hn
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have : IsAffineHom H.X.hom := hi.isAffineHom
  have : Smooth H.X.hom := hs
  have : ConnectedSpace H.X.left := hc
  obtain ⟨hbSurjective, hbFlat, hbQuasiCompact⟩ := fieldExtension_fpqc k K
  let : Surjective b := hbSurjective
  let : Flat b := hbFlat
  let : QuasiCompact b := hbQuasiCompact
  have hsm : Smooth ((GroupScheme.baseChange b).obj H).X.hom := by
    change Smooth (pullback.snd H.X.hom b)
    infer_instance
  have hconn : ConnectedSpace ((GroupScheme.baseChange b).obj H).X.left :=
    H.connectedSpace_baseChange_of_smooth_affine b
  have huni : IsUnipotent ((GroupScheme.baseChange b).obj H) := hu.baseChange
  have hnormal : (SubgroupFunctor.range ((GroupScheme.baseChange b).map i)).IsNormal := by
    rw [SubgroupFunctor.range_baseChangeHom]
    exact hn.baseChange b
  have hrange := h ((GroupScheme.baseChange b).obj H) ((GroupScheme.baseChange b).map i)
    (hi.baseChange b) hsm hconn huni hnormal
  rw [SubgroupFunctor.range_baseChangeHom] at hrange
  exact SubgroupFunctor.eq_bot_of_baseChange_eq_bot b hrange

/-- Connected reductivity is reflected by every field extension, with no hypothesis on
the original group. -/
theorem IsConnectedReductive.of_fieldExtension
    {G : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G)) :
    IsConnectedReductive G := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  obtain ⟨hbSurjective, hbFlat, hbQuasiCompact⟩ := fieldExtension_fpqc k K
  let : Surjective b := hbSurjective
  let : Flat b := hbFlat
  let : QuasiCompact b := hbQuasiCompact
  have hsmooth : Smooth G.X.hom := smooth_of_baseChange b G hG.smooth
  have hconn : ConnectedSpace G.X.left := connectedSpace_of_baseChange b G hG.connectedSpace
  let : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := hG.isAffineHom
  have hAff : IsAffine ((GroupScheme.baseChange b).obj G).X.left :=
    isAffine_of_isAffineHom ((GroupScheme.baseChange b).obj G).X.hom
  change IsAffine (pullback G.X.hom b) at hAff
  let : IsAffine G.X.left :=
    Langlands.AlgebraicGeometry.fieldExtensionAffineDescent k K G.X.left G.X.hom hAff
  have haff : IsAffineHom G.X.hom := inferInstance
  refine ⟨hsmooth, haff, hconn, ?_⟩
  let : Algebra k (AlgebraicClosure K) :=
    ((algebraMap K (AlgebraicClosure K)).comp (algebraMap k K)).toAlgebra
  let ι : AlgebraicClosure k →ₐ[k] AlgebraicClosure K := IsAlgClosed.lift
  let : Algebra (AlgebraicClosure k) (AlgebraicClosure K) := ι.toRingHom.toAlgebra
  let c := toAlgebraicClosure K
  let a := toAlgebraicClosure k
  let d := Spec.map (CommRingCat.ofHom (algebraMap (AlgebraicClosure k) (AlgebraicClosure K)))
  have hcomp : c ≫ b = d ≫ a := by
    dsimp [a, b, c, d, toAlgebraicClosure]
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp]
    apply congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    exact RingHom.ext fun x => (ι.commutes x).symm
  have htotal : HasTrivialUnipotentRadical ((GroupScheme.baseChange (c ≫ b)).obj G) :=
    HasTrivialUnipotentRadical.of_iso (baseChangeCompIso b c G)
      hG.hasTrivialGeometricUnipotentRadical
  rw [hcomp] at htotal
  have hiter : HasTrivialUnipotentRadical
      ((GroupScheme.baseChange d).obj ((GroupScheme.baseChange a).obj G)) :=
    HasTrivialUnipotentRadical.of_iso (baseChangeCompIso a d G).symm htotal
  have : IsAffineHom ((GroupScheme.baseChange a).obj G).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom a)
    infer_instance
  exact HasTrivialUnipotentRadical.of_fieldExtension hiter

/-- Semisimplicity is reflected by every field extension. -/
theorem IsSemisimple.of_fieldExtension
    {G : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsSemisimple
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G)) :
    IsSemisimple G :=
  ⟨IsConnectedReductive.of_fieldExtension hG.isConnectedReductive,
    hG.hasFiniteCenter_of_fieldExtension⟩

/-- Proof of `SemisimpleFieldReflectionStatement`. -/
theorem semisimpleFieldReflectionStatement : SemisimpleFieldReflectionStatement.{u} := by
  intro k K _ _ _ G hG
  exact IsSemisimple.of_fieldExtension hG

end Langlands.GroupScheme
