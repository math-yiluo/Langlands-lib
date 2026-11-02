import Langlands.AlgebraicGeometry.Modules.FinitePresentationPullback

/-! # Pullback of module sheaves preserves quasi-coherence -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- Quasi-coherent data for `M` pulls back to quasi-coherent data for `f^*M`, indexed by the
inverse images of its opens. -/
def pullbackQuasicoherentData (f : X ⟶ Y) {M : Y.Modules} (q : M.QuasicoherentData) :
    ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M).QuasicoherentData where
  I := q.I
  X i := f ⁻¹ᵁ q.X i
  coversTop := (_root_.Opens.coversTop_iff X _).2
    (f.iSup_preimage_eq_top ((_root_.Opens.coversTop_iff Y q.X).1 q.coversTop))
  presentation i :=
    Langlands.AlgebraicGeometry.Modules.presentationPullbackOver f M (q.X i) (q.presentation i)

/-- The pullback of a quasi-coherent module sheaf along any morphism of schemes is
quasi-coherent. -/
instance isQuasicoherent_pullback (f : X ⟶ Y) (M : Y.Modules) [M.IsQuasicoherent] :
    ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M).IsQuasicoherent :=
  (pullbackQuasicoherentData f
    (SheafOfModules.IsQuasicoherent.nonempty_quasicoherentData (M := M)).some).isQuasicoherent

end Langlands.Scheme.Modules
