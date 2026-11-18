import Langlands.GroupScheme.SimplyConnected.DescendedComponentPinning
import Langlands.GroupScheme.CentralIsogeny.TitsComponentTransport

/-! # Actual simply connected factors realizing semisimple Tits components -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

namespace Langlands.GroupScheme

/-- Each entire actual Cartan component of a simply connected group is realized
by its selected geometric factor over the exact finite separable stabilizer field. -/
theorem simplyConnectedTitsComponentFactor :
    SimplyConnectedTitsComponentFactorStatement.{u} := by
  intro k _ G _ _ d hSC a
  let L := SeparableClosure k
  have hSCL := isSimplyConnectedFieldExtension k L G hSC
  let : Smooth G.X.hom := hSC.isSemisimple.isConnectedReductive.smooth
  let : IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k L)).obj G).X.hom :=
    hSCL.isSemisimple.isConnectedReductive.isAffineHom
  let : Smooth ((GroupScheme.baseChange (algebraBaseMap k L)).obj G).X.hom :=
    hSCL.isSemisimple.isConnectedReductive.smooth
  let D := hSCL.almostSimpleProduct
  obtain ⟨F⟩ := d.nonempty_descendedComponentPinning D hSCL.isSemisimple hSC a
  exact ⟨d.componentFactorOfPinningComparison a D hSCL.isSemisimple hSC F⟩

/-- Every entire actual Cartan component of a semisimple group is realized by
an actual absolutely almost-simple simply connected factor over a finite
separable extension, retaining its central cover, ordered Cartan matrix,
both full simultaneous star-image lifts and anisotropy. -/
theorem semisimpleTitsComponentFactor :
    SemisimpleTitsComponentFactorStatement.{u} :=
  semisimpleTitsComponentFactor_of_simplyConnected simplyConnectedTitsComponentFactor

end Langlands.GroupScheme
