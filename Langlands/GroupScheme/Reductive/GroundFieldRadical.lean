import Langlands.GroupScheme.Reductive.UnipotentFieldExtensionStatement
import Langlands.GroupScheme.GeometricConnectedness
import Langlands.GroupScheme.SubgroupFunctor.FpqcDescent

/-! # Ground-field radical triviality from preservation of unipotence -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Fpqc base change reflects triviality of any subgroup functor. -/
theorem SubgroupFunctor.eq_bot_of_baseChange_eq_bot
    {S S' : Scheme.{u}} {G : GroupScheme S} (b : S' ⟶ S)
    [QuasiCompact b] [Flat b] [Surjective b]
    {F : SubgroupFunctor G} (hF : F.baseChange b = ⊥) : F = ⊥ := by
  apply SubgroupFunctor.ext
  intro T
  apply le_antisymm ?_ bot_le
  intro x hx
  change x = 1
  let V : Over S' := (Over.pullback b).obj T
  let q : (Over.map b).obj V ⟶ T :=
    Over.homMk (pullback.fst T.hom b) pullback.condition
  have : EffectiveEpi q.left := by
    change EffectiveEpi (pullback.fst T.hom b)
    infer_instance
  have : Epi q := Over.epi_of_epi_left q
  let x' := (baseChangePointsEquiv b G V).symm (q ≫ x)
  have hx' : x' ∈ (F.baseChange b).carrier V := by
    rw [SubgroupFunctor.mem_baseChange]
    simpa only [x', MulEquiv.apply_symm_apply] using F.comp_mem q hx
  rw [hF] at hx'
  have hx'0 : x' = 1 := by
    simpa only [SubgroupFunctor.bot_carrier, Subgroup.mem_bot] using hx'
  have hqx : q ≫ x = 1 := by
    simpa only [x', MulEquiv.apply_symm_apply, map_one] using
      congrArg (baseChangePointsEquiv b G V) hx'0
  apply (cancel_epi q).mp
  simpa only [MonObj.comp_one] using hqx

/-- Preservation of unipotence supplies the one structural input needed to
descend geometric radical triviality to the ground field. -/
theorem IsConnectedReductive.hasTrivialUnipotentRadical_of_unipotentFieldExtension
    (hU : UnipotentFieldExtensionStatement.{u})
    {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G) : HasTrivialUnipotentRadical G := by
  intro H i hi hs hc hu hn
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : IsClosedImmersion i.hom.hom.left := hi
  have : IsAffineHom H.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  have : Smooth H.X.hom := hs
  have : ConnectedSpace H.X.left := hc
  let b := toAlgebraicClosure k
  have hflat : Flat b ∧ Surjective b :=
    (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom
      (algebraMap k (AlgebraicClosure k)))).mpr
        (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
  have : Flat b := hflat.1
  have : Surjective b := hflat.2
  have : QuasiCompact b := by dsimp [b, toAlgebraicClosure]; infer_instance
  have hsm : Smooth ((GroupScheme.baseChange b).obj H).X.hom := by
    change Smooth (pullback.snd H.X.hom b)
    infer_instance
  have hconn : ConnectedSpace ((GroupScheme.baseChange b).obj H).X.left :=
    H.connectedSpace_baseChange_of_smooth_affine b
  have huni : IsUnipotent ((GroupScheme.baseChange b).obj H) :=
    hU k (AlgebraicClosure k) H inferInstance inferInstance hu
  have hnormal : (SubgroupFunctor.range ((GroupScheme.baseChange b).map i)).IsNormal := by
    rw [SubgroupFunctor.range_baseChangeHom]
    exact hn.baseChange b
  have hrange := hG.hasTrivialGeometricUnipotentRadical
    ((GroupScheme.baseChange b).obj H) ((GroupScheme.baseChange b).map i)
    (hi.baseChange b) hsm hconn huni hnormal
  rw [SubgroupFunctor.range_baseChangeHom] at hrange
  exact SubgroupFunctor.eq_bot_of_baseChange_eq_bot b hrange

/-- The identity on underlying group schemes embeds connected reductive
groups into pseudo-reductive groups, conditional on preservation of unipotence. -/
def connectedReductiveToPseudoReductive
    (hU : UnipotentFieldExtensionStatement.{u})
    (k : Type u) [Field k] :
    {G : GroupScheme (Spec (CommRingCat.of k)) // IsConnectedReductive G} ↪
      {G : GroupScheme (Spec (CommRingCat.of k)) // IsPseudoReductive G} where
  toFun G := ⟨G.val, {
    smooth := G.property.smooth
    isAffineHom := G.property.isAffineHom
    connectedSpace := G.property.connectedSpace
    hasTrivialUnipotentRadical :=
      G.property.hasTrivialUnipotentRadical_of_unipotentFieldExtension hU }⟩
  inj' := by
    intro G H h
    exact Subtype.ext (congrArg
      (fun Z : {G : GroupScheme (Spec (CommRingCat.of k)) //
        IsPseudoReductive G} => Z.val) h)

end Langlands.GroupScheme
