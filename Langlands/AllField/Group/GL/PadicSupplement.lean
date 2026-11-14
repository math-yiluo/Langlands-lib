import Langlands.Group.GL.Padic
import Langlands.AllField.Group.GL.Padic
/-!
# General linear groups over every finite p-adic extension

These explicit structures install the topology of a supplied `TopologicalData`
on the actual matrix unit group. The canonical specialization needs only the
algebraic `PadicField`.
-/

namespace Langlands

universe u

variable {F : Type u} [Field F]

namespace LocalFieldData
open Langlands.LocalFieldData

end LocalFieldData

end Langlands
