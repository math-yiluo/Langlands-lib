import Langlands.GroupScheme.IdentityComponent.Transport
import Langlands.GroupScheme.SimplyConnected.AlmostSimpleFactorDescentProperties

/-! # Descent of almost simplicity for identity components -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.IdentityComponent

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [Smooth G.X.hom] [IsAffineHom G.X.hom]

/-- Almost simplicity of the identity component reflects along any field extension. -/
theorem isAlmostSimple_of_fieldExtension
    (hG : IsAlmostSimple
      (identityComponent ((GroupScheme.baseChange (algebraBaseMap k L)).obj G))) :
    IsAlmostSimple (identityComponent G) :=
  IsAlmostSimple.of_fieldExtension
    (hG.of_iso (baseChangeIso G (algebraMap k L)))

/-- Absolute almost simplicity of the identity component reflects along any field
extension. -/
theorem isAbsolutelyAlmostSimple_of_fieldExtension
    (hG : IsAbsolutelyAlmostSimple
      (identityComponent ((GroupScheme.baseChange (algebraBaseMap k L)).obj G))) :
    IsAbsolutelyAlmostSimple (identityComponent G) :=
  IsAbsolutelyAlmostSimple.of_fieldExtension
    (hG.of_iso (baseChangeIso G (algebraMap k L)))

omit [Smooth G.X.hom] in
/-- An actual comparison with a smooth affine group after field extension descends
smoothness and absolute almost simplicity of the identity component together. -/
theorem smooth_and_isAbsolutelyAlmostSimple_of_fieldExtension_iso
    {H : GroupScheme (Spec (CommRingCat.of L))}
    [Smooth H.X.hom] [IsAffineHom H.X.hom]
    (e : (GroupScheme.baseChange (algebraBaseMap k L)).obj G ≅ H)
    (hH : IsAbsolutelyAlmostSimple (identityComponent H)) :
    ∃ hG : Smooth G.X.hom,
      letI := hG
      IsAbsolutelyAlmostSimple (identityComponent G) := by
  let b := algebraBaseMap k L
  let : Surjective b := (fieldExtension_fpqc k L).1
  let : Flat b := (fieldExtension_fpqc k L).2.1
  let : QuasiCompact b := (fieldExtension_fpqc k L).2.2
  have hsm : Smooth ((GroupScheme.baseChange b).obj G).X.hom := by
    have : IsIso e.hom.hom.hom.left :=
      inferInstanceAs (IsIso (((Grp.forget (Over _)) ⋙ Over.forget _).map e.hom))
    rw [← Over.w e.hom.hom.hom]
    infer_instance
  let : Smooth G.X.hom := smooth_of_baseChange b G hsm
  refine ⟨inferInstance, ?_⟩
  apply isAbsolutelyAlmostSimple_of_fieldExtension (L := L)
  exact hH.of_iso (mapIso e)

end Langlands.GroupScheme.IdentityComponent
