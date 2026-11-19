# Products along a finite involution

Let \(f\) be a family in a commutative group indexed by a finite set with involution \(s\). Suppose \(f(s(i))=\tau(f(i))\) for a group endomorphism \(\tau\). The product of the family equals the product at the fixed indices times a single factor \(x\tau(x)\).

The Lean proof passes to the quotient by the image of \(x\mapsto x\tau(x)\). On the indices moved by \(s\), the two factors from each pair multiply to the unit of the quotient. The product over the moved indices therefore lies in the image, and multiplying by the fixed factors gives the claimed equality.
