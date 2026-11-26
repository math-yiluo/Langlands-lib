# Universe lift of module sheaves

`moduleSheafUniverseLift` applies the module universe lift to every section module and restriction map of a sheaf, keeping the same coefficient ring. The target universe includes the object and morphism universes of the site. To check the sheaf condition at this size, the source forgetful functor preserves the required limits by the free-module adjunction. The lift of underlying types also preserves them. The target forgetful functor reflects these limits, so the module lift preserves sheaves. Postcomposition is fully faithful because the lift on modules is fully faithful.

This categorical change of universe allows published small algebraic coefficient modules to be used in site constructions whose Kan extensions need larger section modules.
